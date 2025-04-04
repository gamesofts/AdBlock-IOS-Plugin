#import <Foundation/Foundation.h>
#import <CoreFoundation/CoreFoundation.h>
#import <CFNetwork/CFNetwork.h>
#import <WebKit/WebKit.h>
#import <objc/runtime.h>
#import <objc/message.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <netdb.h>
#include <errno.h>
#include <ctype.h>
#include <dns_sd.h>
#include <pthread.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <stdatomic.h>
#include "fishhook.h"
#import "domain_list.h"

#define DNS_CACHE_SIZE 2048
#define MAX_DOMAIN_LENGTH 256
#define CACHE_MUTEX_COUNT 64
#define BLOOM_FILTER_SIZE (1 << 20)
#define BLOOM_FILTER_HASH_COUNT 4

typedef struct dns_cache_entry {
    char domain[MAX_DOMAIN_LENGTH];
    int blocked;
    uint64_t last_access;
    uint32_t hash;
    struct dns_cache_entry *next;
} dns_cache_entry_t;

typedef struct RadixChild {
    unsigned char c;
    struct RadixNode *child;
} RadixChild;

typedef struct RadixNode {
    RadixChild *children;
    int childCount;
    int capacity;
    uint8_t is_end;
} RadixNode;

static _Atomic(dns_cache_entry_t *) *dns_cache = NULL;
static uint64_t cache_access_counter = 0;
static pthread_mutex_t cache_mutex[CACHE_MUTEX_COUNT];
static pthread_once_t init_once = PTHREAD_ONCE_INIT;
static RadixNode *domain_trie_root = NULL;
static uint8_t *bloom_filter = NULL;

static int (*orig_connect)(int, const struct sockaddr *, socklen_t) = NULL;
static int (*orig_connectx)(int, const struct sockaddr *, socklen_t, const struct sockaddr *, socklen_t, void *, uint32_t, void *, uint32_t, uint32_t) = NULL;
static ssize_t (*orig_sendto)(int, const void *, size_t, int, const struct sockaddr *, socklen_t) = NULL;
static ssize_t (*orig_send)(int, const void *, size_t, int) = NULL;
static ssize_t (*orig_sendmsg)(int, const struct msghdr *, int) = NULL;
static ssize_t (*orig_write)(int, const void *, size_t) = NULL;
static Boolean (*orig_CFSocketConnectToAddress)(CFSocketRef, CFDataRef) = NULL;
static CFSocketError (*orig_CFSocketSendData)(CFSocketRef, CFDataRef, CFDataRef, double) = NULL;
static Boolean (*orig_CFNetServiceSetClient)(CFNetServiceRef, CFNetServiceClientCallBack, CFNetServiceClientContext *) = NULL;
static CFNetServiceRef (*orig_CFNetServiceCreate)(CFAllocatorRef, CFStringRef, CFStringRef, CFStringRef, SInt32) = NULL;
static Boolean (*orig_CFNetServiceResolveWithTimeout)(CFNetServiceRef, CFTimeInterval, CFStreamError *) = NULL;
static void (*orig_CFStreamCreatePairWithSocketToHost)(CFAllocatorRef, CFStringRef, UInt32, CFReadStreamRef _Nullable *, CFWriteStreamRef _Nullable *) = NULL;
static CFReadStreamRef (*orig_CFStreamCreateForHTTPRequest)(CFAllocatorRef, CFHTTPMessageRef) = NULL;
static CFHTTPMessageRef (*orig_CFHTTPMessageCreateRequest)(CFAllocatorRef, CFStringRef, CFURLRef, CFStringRef) = NULL;

static IMP orig_NSNetServiceInitWithDomain = NULL;
static IMP orig_NSNetServiceInitWithDomainService = NULL;
static IMP orig_NSNetServiceResolve = NULL;
static IMP orig_NSURLSessionDataTaskWithURL = NULL;
static IMP orig_NSURLSessionDataTaskWithURLCompletion = NULL;
static IMP orig_NSURLSessionDataTaskWithRequest = NULL;
static IMP orig_NSURLSessionDataTaskWithRequestCompletion = NULL;
static IMP orig_NSURLSessionDownloadTaskWithURL = NULL;
static IMP orig_NSURLSessionDownloadTaskWithRequest = NULL;
static IMP orig_NSURLSessionUploadTaskWithRequestFromFile = NULL;
static IMP orig_NSURLSessionUploadTaskWithRequestFromData = NULL;
static IMP orig_NSURLSessionUploadTaskWithStreamedRequest = NULL;
static IMP orig_NSURLSessionStreamTaskWithHostNamePort = NULL;
static IMP orig_NSURLSessionStreamTaskWithNetService = NULL;
static IMP orig_NSURLSessionWebSocketTaskWithURL = NULL;
static IMP orig_NSURLSessionWebSocketTaskWithURLProtocols = NULL;
static IMP orig_NSURLConnectionSendSynchronousRequest = NULL;
static IMP orig_NSURLConnectionSendAsynchronousRequest = NULL;
static IMP orig_NSURLConnectionInitWithRequest = NULL;
static IMP orig_NSURLConnectionInitWithRequestStartImmediately = NULL;
static IMP orig_NSURLConnectionConnectionWithRequestDelegate = NULL;
static IMP orig_WKWebViewLoadRequest = NULL;

static inline void CFStringToBuffer(CFStringRef string, char *buffer, size_t bufferSize) {
    if (string && buffer && bufferSize > 0) {
        if (!CFStringGetCString(string, buffer, bufferSize, kCFStringEncodingUTF8)) {
            buffer[0] = '\0';
        }
    } else if (buffer && bufferSize > 0) {
        buffer[0] = '\0';
    }
}

__attribute__((always_inline))
static inline uint32_t fnv1a_hash(const char *str) {
    uint32_t hash = 2166136261u;
    for (; *str; ++str) {
        hash ^= (uint8_t)tolower(*str);
        hash *= 16777619;
    }
    return hash;
}

static void bloom_filter_init(void) {
    size_t bytes = BLOOM_FILTER_SIZE / 8;
    bloom_filter = (uint8_t *)calloc(bytes, 1);
}

__attribute__((always_inline))
static inline uint32_t bloom_hash1(const char *str) {
    return fnv1a_hash(str);
}

__attribute__((always_inline))
static inline uint32_t bloom_hash2(const char *str) {
    uint32_t hash = 5381;
    for (; *str; str++) {
        hash = ((hash << 5) + hash) + (unsigned char)tolower(*str);
    }
    return hash;
}

static void bloom_filter_add(const char *str) {
    if (!str || !bloom_filter) return;
    uint32_t h1 = bloom_hash1(str);
    uint32_t h2 = bloom_hash2(str);
    for (int i = 0; i < BLOOM_FILTER_HASH_COUNT; i++) {
        uint32_t combined = h1 + i * h2;
        uint32_t bitIndex = combined % BLOOM_FILTER_SIZE;
        bloom_filter[bitIndex / 8] |= (1 << (bitIndex % 8));
    }
}

__attribute__((always_inline))
static inline int bloom_filter_check(const char *str) {
    if (!str || !bloom_filter) return 0;
    uint32_t h1 = bloom_hash1(str);
    uint32_t h2 = bloom_hash2(str);
    for (int i = 0; i < BLOOM_FILTER_HASH_COUNT; i++) {
        uint32_t combined = h1 + i * h2;
        uint32_t bitIndex = combined % BLOOM_FILTER_SIZE;
        if ((bloom_filter[bitIndex / 8] & (1 << (bitIndex % 8))) == 0) {
            return 0;
        }
    }
    return 1;
}

static void dns_cache_init(void) {
    dns_cache = calloc(DNS_CACHE_SIZE, sizeof(_Atomic(dns_cache_entry_t *)));
    for (int i = 0; i < CACHE_MUTEX_COUNT; i++) {
        pthread_mutex_init(&cache_mutex[i], NULL);
    }
}

__attribute__((always_inline))
static inline int dns_cache_lookup(const char *domain, int *blocked) {
    if (!domain) return 0;
    
    uint32_t hash = fnv1a_hash(domain);
    unsigned int bucket = hash % DNS_CACHE_SIZE;
    dns_cache_entry_t *entry = atomic_load_explicit(&dns_cache[bucket], memory_order_acquire);
    while (entry) {
        if (entry->hash == hash && strcmp(entry->domain, domain) == 0) {
            __atomic_fetch_add(&cache_access_counter, 1, __ATOMIC_RELAXED);
            *blocked = entry->blocked;
            return 1;
        }
        entry = entry->next;
    }
    return 0;
}

static void dns_cache_insert(const char *domain, int blocked) {
    if (!domain) return;
    
    uint32_t hash = fnv1a_hash(domain);
    unsigned int bucket = hash % DNS_CACHE_SIZE;
    unsigned int mutex_idx = hash % CACHE_MUTEX_COUNT;
    
    pthread_mutex_lock(&cache_mutex[mutex_idx]);
    dns_cache_entry_t *entry = atomic_load_explicit(&dns_cache[bucket], memory_order_relaxed);
    while (entry) {
        if (entry->hash == hash && strcmp(entry->domain, domain) == 0) {
            entry->blocked = blocked;
            entry->last_access = __atomic_fetch_add(&cache_access_counter, 1, __ATOMIC_RELAXED);
            pthread_mutex_unlock(&cache_mutex[mutex_idx]);
            return;
        }
        entry = entry->next;
    }
    dns_cache_entry_t *new_entry = malloc(sizeof(dns_cache_entry_t));
    strlcpy(new_entry->domain, domain, MAX_DOMAIN_LENGTH);
    new_entry->blocked = blocked;
    new_entry->hash = hash;
    new_entry->last_access = __atomic_fetch_add(&cache_access_counter, 1, __ATOMIC_RELAXED);
    new_entry->next = atomic_load_explicit(&dns_cache[bucket], memory_order_relaxed);
    atomic_store_explicit(&dns_cache[bucket], new_entry, memory_order_release);
    pthread_mutex_unlock(&cache_mutex[mutex_idx]);
}

__attribute__((always_inline))
static inline int search_domain(const RadixNode *root, const char *hostname) {
    if (!root || !hostname) return 0;
    int len = (int)strlen(hostname);
    const RadixNode *node = root;
    for (int i = len - 1; i >= 0; i--) {
        unsigned char c = (unsigned char)tolower(hostname[i]);
        const RadixNode *child = NULL;
        for (int j = 0; j < node->childCount; j++) {
            if (node->children[j].c == c) {
                child = node->children[j].child;
                break;
            }
        }
        if (!child) {
            if (c == '.' && node->is_end) {
                return 1;
            }
            return 0;
        }
        node = child;
        if (node->is_end && (i == 0 || hostname[i - 1] == '.')) {
            return 1;
        }
    }
    return node->is_end;
}

static RadixNode *create_radix_node(void) {
    RadixNode *node = calloc(1, sizeof(RadixNode));
    return node;
}

static RadixNode *get_child(RadixNode *node, unsigned char c) {
    for (int i = 0; i < node->childCount; i++) {
        if (node->children[i].c == c) {
            return node->children[i].child;
        }
    }
    return NULL;
}

static RadixNode *add_child(RadixNode *node, unsigned char c) {
    if (node->childCount == node->capacity) {
        int newCapacity = (node->capacity == 0) ? 4 : node->capacity * 2;
        node->children = realloc(node->children, newCapacity * sizeof(RadixChild));
        node->capacity = newCapacity;
    }
    RadixNode *child = create_radix_node();
    node->children[node->childCount].c = c;
    node->children[node->childCount].child = child;
    node->childCount++;
    return child;
}

static void radix_insert(RadixNode *root, const char *domain) {
    if (!root || !domain) return;
    int len = (int)strlen(domain);
    RadixNode *node = root;
    for (int i = len - 1; i >= 0; i--) {
        unsigned char c = (unsigned char)tolower(domain[i]);
        RadixNode *child = get_child(node, c);
        if (!child) {
            child = add_child(node, c);
        }
        node = child;
    }
    node->is_end = 1;
}

static void build_domain_trie(void) {
    const char *list = embedded_domain_list;
    if (!list) return;
    
    domain_trie_root = create_radix_node();
    bloom_filter_init();
    
    const char *start = list;
    const char *end;
    while (*start) {
        end = strchr(start, '\n');
        if (!end) end = start + strlen(start);
        int len = end - start;
        if (len > 0 && len < MAX_DOMAIN_LENGTH) {
            char domain[MAX_DOMAIN_LENGTH];
            memcpy(domain, start, len);
            domain[len] = '\0';
            radix_insert(domain_trie_root, domain);
            bloom_filter_add(domain);
        }
        if (*end == '\0') break;
        start = end + 1;
    }
}

static int is_domain_blocked(const char *hostname) {
    if (!hostname) return 0;
    
    int cached;
    if (dns_cache_lookup(hostname, &cached)) {
        return cached;
    }

    const char *p = hostname;
    int bloom_hit = 0;
    while (p) {
        if (bloom_filter_check(p)) {
            bloom_hit = 1;
            break;
        }
        p = strchr(p, '.');
        if (p) p++;
    }
    if (!bloom_hit) {
        dns_cache_insert(hostname, 0);
        return 0;
    }
    
    int blocked = search_domain(domain_trie_root, hostname);
    dns_cache_insert(hostname, blocked);
    return blocked;
}

static int extract_host_from_sockaddr(const struct sockaddr *addr, char *host, size_t hostlen) {
    if (addr->sa_family == AF_INET) {
        struct sockaddr_in *sin = (struct sockaddr_in *)addr;
        if (!inet_ntop(AF_INET, &sin->sin_addr, host, hostlen)) {
            return 0;
        }
        return 1;
    } else if (addr->sa_family == AF_INET6) {
        struct sockaddr_in6 *sin6 = (struct sockaddr_in6 *)addr;
        if (!inet_ntop(AF_INET6, &sin6->sin6_addr, host, hostlen)) {
            return 0;
        }
        return 1;
    }
    return 0;
}

static int resolve_address_to_hostname(const struct sockaddr *addr, char *hostname, size_t hostlen) {
    if (!addr || !hostname || hostlen < 1) return 0;
    
    char ipstr[INET6_ADDRSTRLEN] = {0};
    if (!extract_host_from_sockaddr(addr, ipstr, sizeof(ipstr))) {
        return 0;
    }
    NSString *ipKey = [NSString stringWithUTF8String:ipstr];
    static NSCache *resolveCache = nil;
    static dispatch_once_t onceToken;
    dispatch_once(&onceToken, ^{
        resolveCache = [[NSCache alloc] init];
        resolveCache.countLimit = DNS_CACHE_SIZE;
    });
    
    NSString *cachedName = [resolveCache objectForKey:ipKey];
    if (cachedName) {
        strlcpy(hostname, [cachedName UTF8String], hostlen);
        return 1;
    }
    
    struct addrinfo hints, *result = NULL;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = addr->sa_family;
    hints.ai_flags = AI_CANONNAME;
    hints.ai_socktype = SOCK_STREAM;
    
    int error = getaddrinfo(ipstr, NULL, &hints, &result);
    NSString *canonName = nil;
    if (error != 0 || !result) {
        canonName = [NSString stringWithUTF8String:ipstr];
    } else if (result->ai_canonname && strlen(result->ai_canonname) > 0) {
        canonName = [NSString stringWithUTF8String:result->ai_canonname];
    } else {
        canonName = [NSString stringWithUTF8String:ipstr];
    }
    
    [resolveCache setObject:canonName forKey:ipKey];
    strlcpy(hostname, [canonName UTF8String], hostlen);
    if (result) freeaddrinfo(result);
    return 1;
}

static inline int is_sockaddr_blocked(const struct sockaddr *addr) {
    if (!addr) return 0;
    char hostname[NI_MAXHOST] = {0};
    if (resolve_address_to_hostname(addr, hostname, sizeof(hostname)) && is_domain_blocked(hostname)) {
         return 1;
    }
    return 0;
}

static inline int is_sockfd_blocked(int sockfd) {
    struct sockaddr_storage addr;
    socklen_t addrlen = sizeof(addr);
    if (getpeername(sockfd, (struct sockaddr *)&addr, &addrlen) == 0) {
         return is_sockaddr_blocked((struct sockaddr *)&addr);
    }
    return 0;
}

static inline BOOL is_url_blocked(NSURL *url) {
    if (!url) return NO;
    NSString *host = url.host;
    if (!host) return NO;
    char hostStr[MAX_DOMAIN_LENGTH] = {0};
    strlcpy(hostStr, [host UTF8String], MAX_DOMAIN_LENGTH);
    return is_domain_blocked(hostStr) ? YES : NO;
}

static inline BOOL is_host_blocked(CFStringRef host) {
    char hostBuf[MAX_DOMAIN_LENGTH] = {0};
    if (host) {
       CFStringToBuffer(host, hostBuf, MAX_DOMAIN_LENGTH);
       if (hostBuf[0] && is_domain_blocked(hostBuf)) return YES;
    }
    return NO;
}

int my_connect(int socket, const struct sockaddr *address, socklen_t address_len) {
    if (is_sockaddr_blocked(address)) {
        errno = EHOSTUNREACH;
        return -1;
    }
    return orig_connect(socket, address, address_len);
}

int my_connectx(int socket,
                const struct sockaddr *local, socklen_t local_len,
                const struct sockaddr *remote, socklen_t remote_len,
                void *header, uint32_t header_size,
                void *trailer, uint32_t trailer_size,
                uint32_t flags) {
    if (is_sockaddr_blocked(remote)) {
        errno = EHOSTUNREACH;
        return -1;
    }
    return orig_connectx(socket, local, local_len, remote, remote_len,
                         header, header_size, trailer, trailer_size, flags);
}

ssize_t my_sendto(int socket, const void *buffer, size_t length, int flags,
                  const struct sockaddr *dest_addr, socklen_t dest_len) {
    if (is_sockaddr_blocked(dest_addr)) {
        errno = EHOSTUNREACH;
        return -1;
    }
    return orig_sendto(socket, buffer, length, flags, dest_addr, dest_len);
}

ssize_t my_send(int sockfd, const void *buf, size_t len, int flags) {
    if (is_sockfd_blocked(sockfd)) {
        errno = EHOSTUNREACH;
        return -1;
    }
    return orig_send(sockfd, buf, len, flags);
}

ssize_t my_sendmsg(int sockfd, const struct msghdr *msg, int flags) {
    if (msg && msg->msg_name) {
        if (is_sockaddr_blocked((const struct sockaddr *)msg->msg_name)) {
            errno = EHOSTUNREACH;
            return -1;
        }
    } else {
        if (is_sockfd_blocked(sockfd)) {
            errno = EHOSTUNREACH;
            return -1;
        }
    }
    return orig_sendmsg(sockfd, msg, flags);
}

ssize_t my_write(int fd, const void *buf, size_t count) {
    struct stat st;
    if (fstat(fd, &st) == 0 && S_ISSOCK(st.st_mode)) {
        if (is_sockfd_blocked(fd)) {
            errno = EHOSTUNREACH;
            return -1;
        }
    }
    return orig_write(fd, buf, count);
}

Boolean my_CFSocketConnectToAddress(CFSocketRef s, CFDataRef address) {
    if (address) {
        const struct sockaddr *addr = (const struct sockaddr *)CFDataGetBytePtr(address);
        if (is_sockaddr_blocked(addr)) {
            return false;
        }
    }
    return orig_CFSocketConnectToAddress(s, address);
}

CFSocketError my_CFSocketSendData(CFSocketRef s, CFDataRef address, CFDataRef data, double timeout) {
    if (address) {
        const struct sockaddr *addr = (const struct sockaddr *)CFDataGetBytePtr(address);
        if (is_sockaddr_blocked(addr)) {
            return kCFSocketError;
        }
    }
    return orig_CFSocketSendData(s, address, data, timeout);
}

CFNetServiceRef my_CFNetServiceCreate(CFAllocatorRef alloc,
                                      CFStringRef domain,
                                      CFStringRef serviceType,
                                      CFStringRef name,
                                      SInt32 port) {
    if (is_host_blocked(domain) || is_host_blocked(name)) {
         return NULL;
    }
    return orig_CFNetServiceCreate(alloc, domain, serviceType, name, port);
}

Boolean my_CFNetServiceSetClient(CFNetServiceRef theService,
                                 CFNetServiceClientCallBack clientCB,
                                 CFNetServiceClientContext *clientContext) {
    if (theService) {
        CFStringRef domain = CFNetServiceGetDomain(theService);
        CFStringRef name = CFNetServiceGetName(theService);
        if (is_host_blocked(domain) || is_host_blocked(name)) {
            return false;
        }
    }
    return orig_CFNetServiceSetClient(theService, clientCB, clientContext);
}

Boolean my_CFNetServiceResolveWithTimeout(CFNetServiceRef theService,
                                          CFTimeInterval timeout,
                                          CFStreamError *error) {
    if (theService) {
        CFStringRef domain = CFNetServiceGetDomain(theService);
        CFStringRef name = CFNetServiceGetName(theService);
        if (is_host_blocked(domain) || is_host_blocked(name)) {
            return false;
        }
    }
    return orig_CFNetServiceResolveWithTimeout(theService, timeout, error);
}

CFReadStreamRef my_CFStreamCreateForHTTPRequest(CFAllocatorRef alloc, CFHTTPMessageRef request) {
    if (request) {
        CFURLRef url = CFHTTPMessageCopyRequestURL(request);
        if (url) {
            CFStringRef host = CFURLCopyHostName(url);
            if (host) {
                if (is_host_blocked(host)) {
                    CFRelease(host);
                    CFRelease(url);
                    return NULL;
                }
                CFRelease(host);
            }
            CFRelease(url);
        }
    }
    return orig_CFStreamCreateForHTTPRequest(alloc, request);
}

void my_CFStreamCreatePairWithSocketToHost(CFAllocatorRef alloc, CFStringRef host, UInt32 port,
                                           CFReadStreamRef  _Nullable *readStream,
                                           CFWriteStreamRef _Nullable *writeStream) {
    if (is_host_blocked(host)) {
        if (readStream) *readStream = NULL;
        if (writeStream) *writeStream = NULL;
        return;
    }
    orig_CFStreamCreatePairWithSocketToHost(alloc, host, port, readStream, writeStream);
}

CFHTTPMessageRef my_CFHTTPMessageCreateRequest(CFAllocatorRef alloc,
                                               CFStringRef requestMethod,
                                               CFURLRef url,
                                               CFStringRef httpVersion) {
    if (url) {
        CFStringRef host = CFURLCopyHostName(url);
        if (host) {
            if (is_host_blocked(host)) {
                CFRelease(host);
                return NULL;
            }
            CFRelease(host);
        }
    }
    return orig_CFHTTPMessageCreateRequest(alloc, requestMethod, url, httpVersion);
}

id my_NSNetServiceInitWithDomain(id self, SEL _cmd, id domain, id type, id name) {
    if (is_host_blocked((__bridge CFStringRef)domain) || is_host_blocked((__bridge CFStringRef)name)) {
        return nil;
    }
    return ((id (*)(id, SEL, id, id, id))orig_NSNetServiceInitWithDomain)(self, _cmd, domain, type, name);
}

id my_NSNetServiceInitWithDomainService(id self, SEL _cmd, id domain, id type, id name, int port) {
    if (is_host_blocked((__bridge CFStringRef)domain) || is_host_blocked((__bridge CFStringRef)name)) {
        return nil;
    }
    return ((id (*)(id, SEL, id, id, id, int))orig_NSNetServiceInitWithDomainService)(self, _cmd, domain, type, name, port);
}

void my_NSNetServiceResolve(id self, SEL _cmd) {
    id domain = [self valueForKey:@"domain"];
    id name = [self valueForKey:@"name"];
    if (is_host_blocked((__bridge CFStringRef)domain) || is_host_blocked((__bridge CFStringRef)name)) {
        id delegate = [self valueForKey:@"delegate"];
        if (delegate && [delegate respondsToSelector:@selector(netService:didNotResolve:)]) {
            NSDictionary *errorDict = @{@"NSNetServicesErrorCode": @(NSNetServicesNotFoundError),
                                       @"NSNetServicesErrorDomain": @"NSNetServicesErrorDomain"};
            [delegate netService:self didNotResolve:errorDict];
        }
        return;
    }
    ((void (*)(id, SEL))orig_NSNetServiceResolve)(self, _cmd);
}

static void blocked_task_cancel(id __unused self, SEL __unused _cmd) {
    if ([self respondsToSelector:@selector(setValue:forKey:)]) {
        NSError *error = [NSError errorWithDomain:NSURLErrorDomain 
                                             code:NSURLErrorCannotConnectToHost 
                                         userInfo:@{NSLocalizedDescriptionKey: @"Connection blocked by content filter"}];
        [self setValue:error forKey:@"error"];
    }
}

static void blocked_task_resume(id self, SEL _cmd) {
    blocked_task_cancel(self, _cmd);
    if ([self respondsToSelector:@selector(delegate)] && [self delegate]) {
        id delegate = [self delegate];
        if ([delegate respondsToSelector:@selector(URLSession:task:didCompleteWithError:)]) {
            NSError *error = [NSError errorWithDomain:NSURLErrorDomain
                                                 code:NSURLErrorCannotConnectToHost
                                             userInfo:@{NSLocalizedDescriptionKey: @"Connection blocked by content filter"}];
            dispatch_async(dispatch_get_main_queue(), ^{
                [delegate URLSession:[NSURLSession sharedSession] task:self didCompleteWithError:error];
            });
        }
    }
}

static id createBlockedURLSessionTask(void) {
    static Class BlockedURLSessionTaskClass = Nil;
    if (!BlockedURLSessionTaskClass) {
        BlockedURLSessionTaskClass = objc_allocateClassPair([NSURLSessionDataTask class], "BlockedURLSessionTask", 0);
        class_addMethod(BlockedURLSessionTaskClass, @selector(resume), (IMP)blocked_task_resume, "v@:");
        class_addMethod(BlockedURLSessionTaskClass, @selector(cancel), (IMP)blocked_task_cancel, "v@:");
        objc_registerClassPair(BlockedURLSessionTaskClass);
    }
    id task = [[BlockedURLSessionTaskClass alloc] init];
    [task cancel];
    return task;
}

id my_NSURLSessionDataTaskWithURL(id self, SEL _cmd, NSURL *url) {
    if (is_url_blocked(url)) {
        return createBlockedURLSessionTask();
    }
    return ((id (*)(id, SEL, NSURL *))orig_NSURLSessionDataTaskWithURL)(self, _cmd, url);
}

id my_NSURLSessionDataTaskWithURLCompletion(id self, SEL _cmd, NSURL *url, void (^completionHandler)(NSData *, NSURLResponse *, NSError *)) {
    if (is_url_blocked(url)) {
        if (completionHandler) {
            NSError *error = [NSError errorWithDomain:NSURLErrorDomain
                                                 code:NSURLErrorCannotConnectToHost
                                             userInfo:@{NSLocalizedDescriptionKey: @"Connection blocked by content filter"}];
            dispatch_async(dispatch_get_main_queue(), ^{
                completionHandler(nil, nil, error);
            });
        }
        return createBlockedURLSessionTask();
    }
    return ((id (*)(id, SEL, NSURL *, void (^)(NSData *, NSURLResponse *, NSError *)))orig_NSURLSessionDataTaskWithURLCompletion)(self, _cmd, url, completionHandler);
}

id my_NSURLSessionDataTaskWithRequest(id self, SEL _cmd, NSURLRequest *request) {
    if (is_url_blocked(request.URL)) {
        return createBlockedURLSessionTask();
    }
    return ((id (*)(id, SEL, NSURLRequest *))orig_NSURLSessionDataTaskWithRequest)(self, _cmd, request);
}

id my_NSURLSessionDataTaskWithRequestCompletion(id self, SEL _cmd, NSURLRequest *request, void (^completionHandler)(NSData *, NSURLResponse *, NSError *)) {
    if (is_url_blocked(request.URL)) {
        if (completionHandler) {
            NSError *error = [NSError errorWithDomain:NSURLErrorDomain
                                                 code:NSURLErrorCannotConnectToHost
                                             userInfo:@{NSLocalizedDescriptionKey: @"Connection blocked by content filter"}];
            dispatch_async(dispatch_get_main_queue(), ^{
                completionHandler(nil, nil, error);
            });
        }
        return createBlockedURLSessionTask();
    }
    return ((id (*)(id, SEL, NSURLRequest *, void (^)(NSData *, NSURLResponse *, NSError *)))orig_NSURLSessionDataTaskWithRequestCompletion)(self, _cmd, request, completionHandler);
}

id my_NSURLSessionDownloadTaskWithURL(id self, SEL _cmd, NSURL *url) {
    if (is_url_blocked(url)) {
        return createBlockedURLSessionTask();
    }
    return ((id (*)(id, SEL, NSURL *))orig_NSURLSessionDownloadTaskWithURL)(self, _cmd, url);
}

id my_NSURLSessionDownloadTaskWithRequest(id self, SEL _cmd, NSURLRequest *request) {
    if (is_url_blocked(request.URL)) {
        return createBlockedURLSessionTask();
    }
    return ((id (*)(id, SEL, NSURLRequest *))orig_NSURLSessionDownloadTaskWithRequest)(self, _cmd, request);
}

id my_NSURLSessionUploadTaskWithRequestFromFile(id self, SEL _cmd, NSURLRequest *request, NSURL *fileURL) {
    if (is_url_blocked(request.URL)) {
        return createBlockedURLSessionTask();
    }
    return ((id (*)(id, SEL, NSURLRequest *, NSURL *))orig_NSURLSessionUploadTaskWithRequestFromFile)(self, _cmd, request, fileURL);
}

id my_NSURLSessionUploadTaskWithRequestFromData(id self, SEL _cmd, NSURLRequest *request, NSData *bodyData) {
    if (is_url_blocked(request.URL)) {
        return createBlockedURLSessionTask();
    }
    return ((id (*)(id, SEL, NSURLRequest *, NSData *))orig_NSURLSessionUploadTaskWithRequestFromData)(self, _cmd, request, bodyData);
}

id my_NSURLSessionUploadTaskWithStreamedRequest(id self, SEL _cmd, NSURLRequest *request) {
    if (is_url_blocked(request.URL)) {
        return createBlockedURLSessionTask();
    }
    return ((id (*)(id, SEL, NSURLRequest *))orig_NSURLSessionUploadTaskWithStreamedRequest)(self, _cmd, request);
}

id my_NSURLSessionStreamTaskWithHostNamePort(id self, SEL _cmd, NSString *hostname, NSInteger port) {
    if (is_host_blocked((__bridge CFStringRef)hostname)) {
        return createBlockedURLSessionTask();
    }
    return ((id (*)(id, SEL, NSString *, NSInteger))orig_NSURLSessionStreamTaskWithHostNamePort)(self, _cmd, hostname, port);
}

id my_NSURLSessionStreamTaskWithNetService(id self, SEL _cmd, NSNetService *service) {
    if (service) {
        NSString *domain = [service domain];
        NSString *name = [service name];
        if (is_host_blocked((__bridge CFStringRef)domain) || is_host_blocked((__bridge CFStringRef)name)) {
            return createBlockedURLSessionTask();
        }
    }
    return ((id (*)(id, SEL, NSNetService *))orig_NSURLSessionStreamTaskWithNetService)(self, _cmd, service);
}

id my_NSURLSessionWebSocketTaskWithURL(id self, SEL _cmd, NSURL *url) {
    if (is_url_blocked(url)) {
        return createBlockedURLSessionTask();
    }
    return ((id (*)(id, SEL, NSURL *))orig_NSURLSessionWebSocketTaskWithURL)(self, _cmd, url);
}

id my_NSURLSessionWebSocketTaskWithURLProtocols(id self, SEL _cmd, NSURL *url, NSArray *protocols) {
    if (is_url_blocked(url)) {
        return createBlockedURLSessionTask();
    }
    return ((id (*)(id, SEL, NSURL *, NSArray *))orig_NSURLSessionWebSocketTaskWithURLProtocols)(self, _cmd, url, protocols);
}

static NSData* my_NSURLConnectionSendSynchronousRequest(Class self, SEL _cmd, NSURLRequest *request, NSURLResponse **response, NSError **error) {
    if (is_url_blocked(request.URL)) {
        if (error) {
            *error = [NSError errorWithDomain:NSURLErrorDomain
                                         code:NSURLErrorCannotConnectToHost
                                     userInfo:@{NSLocalizedDescriptionKey: @"Connection blocked by content filter"}];
        }
        return nil;
    }
    return ((NSData* (*)(Class, SEL, NSURLRequest *, NSURLResponse **, NSError **))orig_NSURLConnectionSendSynchronousRequest)(self, _cmd, request, response, error);
}

void my_NSURLConnectionSendAsyncRequest(Class self, SEL _cmd, NSURLRequest *request,
                                       NSOperationQueue *queue,
                                       void (^completionHandler)(NSURLResponse*, NSData*, NSError*)) {
    if (!queue) {
        queue = [NSOperationQueue mainQueue];
    }
    if (is_url_blocked(request.URL)) {
        NSError *error = [NSError errorWithDomain:NSURLErrorDomain
                                             code:NSURLErrorCannotConnectToHost
                                         userInfo:@{NSLocalizedDescriptionKey: @"Connection blocked by content filter"}];
        if (completionHandler) {
            [queue addOperationWithBlock:^{
                completionHandler(nil, nil, error);
            }];
        }
        return;
    }
    ((void (*)(Class, SEL, NSURLRequest *, NSOperationQueue *, void (^)(NSURLResponse*, NSData*, NSError*)))orig_NSURLConnectionSendAsynchronousRequest)
        (self, _cmd, request, queue, completionHandler);
}

id my_NSURLConnectionInitWithRequest(id self, SEL _cmd, NSURLRequest *request, id delegate) {
    if (is_url_blocked(request.URL)) {
        return nil;
    }
    return ((id (*)(id, SEL, NSURLRequest *, id))orig_NSURLConnectionInitWithRequest)(self, _cmd, request, delegate);
}

id my_NSURLConnectionInitWithRequestStartImmediately(id self, SEL _cmd, NSURLRequest *request, id delegate, BOOL startImmediately) {
    if (is_url_blocked(request.URL)) {
        return nil;
    }
    return ((id (*)(id, SEL, NSURLRequest *, id, BOOL))orig_NSURLConnectionInitWithRequestStartImmediately)(self, _cmd, request, delegate, startImmediately);
}

id my_NSURLConnectionConnectionWithRequestDelegate(Class self, SEL _cmd, NSURLRequest *request, id delegate) {
    if (is_url_blocked(request.URL)) {
        return nil;
    }
    return ((id (*)(Class, SEL, NSURLRequest *, id))orig_NSURLConnectionConnectionWithRequestDelegate)(self, _cmd, request, delegate);
}

void my_WKWebViewLoadRequest(id self, SEL _cmd, NSURLRequest *request) {
    if (is_url_blocked(request.URL)) {
        [self stopLoading];
        id navigationDelegate = [self valueForKey:@"navigationDelegate"];
        if (navigationDelegate && [navigationDelegate respondsToSelector:@selector(webView:didFailNavigation:withError:)]) {
            NSError *error = [NSError errorWithDomain:NSURLErrorDomain
                                                 code:NSURLErrorCannotConnectToHost
                                             userInfo:@{NSLocalizedDescriptionKey: @"Connection blocked by content filter"}];
            [navigationDelegate webView:self didFailNavigation:nil withError:error];
        }
        [(WKWebView *)self loadHTMLString:@"" baseURL:nil];
        return;
    }
    ((void (*)(id, SEL, NSURLRequest *))orig_WKWebViewLoadRequest)(self, _cmd, request);
}

static void swizzleMethod(Class class, SEL originalSelector, IMP replacement, IMP *originalMethod) {
    Method method = class_getInstanceMethod(class, originalSelector);
    if (method) {
        *originalMethod = method_setImplementation(method, replacement);
    }
}

static void swizzleClassMethod(Class class, SEL originalSelector, IMP replacement, IMP *originalMethod) {
    Method method = class_getClassMethod(class, originalSelector);
    if (method) {
        *originalMethod = method_setImplementation(method, replacement);
    }
}

static void free_radix_tree(RadixNode *node) {
    if (!node) return;
    for (int i = 0; i < node->childCount; i++) {
        free_radix_tree(node->children[i].child);
    }
    free(node->children);
    free(node);
}

static void initialize_once(void) {
    dns_cache_init();
    build_domain_trie();
}

__attribute__((constructor))
static void adblock_init(void) {
    pthread_once(&init_once, initialize_once);
    struct rebinding rebindings[] = {
        {"connect", my_connect, (void *)&orig_connect},
        {"connectx", my_connectx, (void *)&orig_connectx},
        {"sendto", my_sendto, (void *)&orig_sendto},
        {"send", my_send, (void *)&orig_send},
        {"sendmsg", my_sendmsg, (void *)&orig_sendmsg},
        {"write", my_write, (void *)&orig_write},
        {"CFSocketConnectToAddress", my_CFSocketConnectToAddress, (void *)&orig_CFSocketConnectToAddress},
        {"CFSocketSendData", my_CFSocketSendData, (void *)&orig_CFSocketSendData},
        {"CFNetServiceCreate", my_CFNetServiceCreate, (void *)&orig_CFNetServiceCreate},
        {"CFNetServiceSetClient", my_CFNetServiceSetClient, (void *)&orig_CFNetServiceSetClient},
        {"CFNetServiceResolveWithTimeout", my_CFNetServiceResolveWithTimeout, (void *)&orig_CFNetServiceResolveWithTimeout},
        {"CFStreamCreatePairWithSocketToHost", my_CFStreamCreatePairWithSocketToHost, (void *)&orig_CFStreamCreatePairWithSocketToHost},
        {"CFStreamCreateForHTTPRequest", my_CFStreamCreateForHTTPRequest, (void *)&orig_CFStreamCreateForHTTPRequest},
        {"CFHTTPMessageCreateRequest", my_CFHTTPMessageCreateRequest, (void *)&orig_CFHTTPMessageCreateRequest}
    };
    
    rebind_symbols(rebindings, sizeof(rebindings)/sizeof(rebindings[0]));
    
    Class nsNetServiceClass = objc_getClass("NSNetService");
    if (nsNetServiceClass) {
        swizzleMethod(nsNetServiceClass,
                      sel_registerName("initWithDomain:type:name:"),
                      (IMP)my_NSNetServiceInitWithDomain,
                      &orig_NSNetServiceInitWithDomain);
        
        swizzleMethod(nsNetServiceClass,
                      sel_registerName("initWithDomain:type:name:port:"),
                      (IMP)my_NSNetServiceInitWithDomainService,
                      &orig_NSNetServiceInitWithDomainService);
        
        swizzleMethod(nsNetServiceClass,
                      sel_registerName("resolve"),
                      (IMP)my_NSNetServiceResolve,
                      &orig_NSNetServiceResolve);
    }
    
    Class urlSessionClass = objc_getClass("NSURLSession");
    if (urlSessionClass) {
        swizzleMethod(urlSessionClass,
                     sel_registerName("dataTaskWithURL:"),
                     (IMP)my_NSURLSessionDataTaskWithURL,
                     &orig_NSURLSessionDataTaskWithURL);
        swizzleMethod(urlSessionClass,
                      sel_registerName("dataTaskWithURL:completionHandler:"),
                      (IMP)my_NSURLSessionDataTaskWithURLCompletion,
                      &orig_NSURLSessionDataTaskWithURLCompletion);
        swizzleMethod(urlSessionClass,
                     sel_registerName("dataTaskWithRequest:"),
                     (IMP)my_NSURLSessionDataTaskWithRequest,
                     &orig_NSURLSessionDataTaskWithRequest);
        swizzleMethod(urlSessionClass,
                      sel_registerName("dataTaskWithRequest:completionHandler:"),
                      (IMP)my_NSURLSessionDataTaskWithRequestCompletion,
                      &orig_NSURLSessionDataTaskWithRequestCompletion);
        swizzleMethod(urlSessionClass,
                     sel_registerName("downloadTaskWithURL:"),
                     (IMP)my_NSURLSessionDownloadTaskWithURL,
                     &orig_NSURLSessionDownloadTaskWithURL);
        swizzleMethod(urlSessionClass,
                     sel_registerName("downloadTaskWithRequest:"),
                     (IMP)my_NSURLSessionDownloadTaskWithRequest,
                     &orig_NSURLSessionDownloadTaskWithRequest);
        swizzleMethod(urlSessionClass,
                      sel_registerName("uploadTaskWithRequest:fromFile:"),
                      (IMP)my_NSURLSessionUploadTaskWithRequestFromFile,
                      &orig_NSURLSessionUploadTaskWithRequestFromFile);
        swizzleMethod(urlSessionClass,
                      sel_registerName("uploadTaskWithRequest:fromData:"),
                      (IMP)my_NSURLSessionUploadTaskWithRequestFromData,
                      &orig_NSURLSessionUploadTaskWithRequestFromData);
        swizzleMethod(urlSessionClass,
                      sel_registerName("uploadTaskWithStreamedRequest:"),
                      (IMP)my_NSURLSessionUploadTaskWithStreamedRequest,
                      &orig_NSURLSessionUploadTaskWithStreamedRequest);
        swizzleMethod(urlSessionClass,
                      sel_registerName("streamTaskWithHostName:port:"),
                      (IMP)my_NSURLSessionStreamTaskWithHostNamePort,
                      &orig_NSURLSessionStreamTaskWithHostNamePort);
        swizzleMethod(urlSessionClass,
                      sel_registerName("streamTaskWithNetService:"),
                      (IMP)my_NSURLSessionStreamTaskWithNetService,
                      &orig_NSURLSessionStreamTaskWithNetService);
        swizzleMethod(urlSessionClass,
                      sel_registerName("webSocketTaskWithURL:"),
                      (IMP)my_NSURLSessionWebSocketTaskWithURL,
                      &orig_NSURLSessionWebSocketTaskWithURL);
        swizzleMethod(urlSessionClass,
                      sel_registerName("webSocketTaskWithURL:protocols:"),
                      (IMP)my_NSURLSessionWebSocketTaskWithURLProtocols,
                      &orig_NSURLSessionWebSocketTaskWithURLProtocols);
    }

    Class urlConnectionClass = objc_getClass("NSURLConnection");
    if (urlConnectionClass) {
        swizzleClassMethod(urlConnectionClass,
                          sel_registerName("sendSynchronousRequest:returningResponse:error:"),
                          (IMP)my_NSURLConnectionSendSynchronousRequest,
                          &orig_NSURLConnectionSendSynchronousRequest);
        swizzleClassMethod(urlConnectionClass,
                          sel_registerName("sendAsynchronousRequest:queue:completionHandler:"),
                          (IMP)my_NSURLConnectionSendAsyncRequest,
                          &orig_NSURLConnectionSendAsynchronousRequest);
        swizzleMethod(urlConnectionClass,
                          sel_registerName("initWithRequest:delegate:"),
                          (IMP)my_NSURLConnectionInitWithRequest,
                          &orig_NSURLConnectionInitWithRequest);
        swizzleMethod(urlConnectionClass,
                          sel_registerName("initWithRequest:delegate:startImmediately:"),
                          (IMP)my_NSURLConnectionInitWithRequestStartImmediately,
                          &orig_NSURLConnectionInitWithRequestStartImmediately);
        swizzleClassMethod(urlConnectionClass,
                          sel_registerName("connectionWithRequest:delegate:"),
                          (IMP)my_NSURLConnectionConnectionWithRequestDelegate,
                          &orig_NSURLConnectionConnectionWithRequestDelegate);
    }
    
    Class wkWebViewClass = objc_getClass("WKWebView");
    if (wkWebViewClass) {
        swizzleMethod(wkWebViewClass,
                      sel_registerName("loadRequest:"),
                      (IMP)my_WKWebViewLoadRequest,
                      &orig_WKWebViewLoadRequest);
    }
}

__attribute__((destructor))
static void adblock_deinit(void) {
    if (domain_trie_root) {
        free_radix_tree(domain_trie_root);
        domain_trie_root = NULL;
    }
    
    if (dns_cache) {
        for (int i = 0; i < DNS_CACHE_SIZE; i++) {
            dns_cache_entry_t *entry = atomic_load_explicit(&dns_cache[i], memory_order_acquire);
            while (entry) {
                dns_cache_entry_t *next = entry->next;
                free(entry);
                entry = next;
            }
        }
        free(dns_cache);
        dns_cache = NULL;
    }
    
    for (int i = 0; i < CACHE_MUTEX_COUNT; i++) {
        pthread_mutex_destroy(&cache_mutex[i]);
    }
    
    if (bloom_filter) {
        free(bloom_filter);
        bloom_filter = NULL;
    }
}
