#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

/* Lean 4.20 asks for /proc/<own-pid>/exe. Some containers expose only
 * /proc/self/exe. Resolve exactly that equivalent self path; leave every
 * other readlink request and the Lean kernel untouched. */
ssize_t readlink(const char *path, char *buf, size_t size) {
    ssize_t (*next_readlink)(const char *, char *, size_t) =
        (ssize_t (*)(const char *, char *, size_t))dlsym(RTLD_NEXT, "readlink");
    char own_path[64];
    snprintf(own_path, sizeof own_path, "/proc/%ld/exe", (long)getpid());
    return next_readlink(strcmp(path, own_path) == 0 ? "/proc/self/exe" : path,
                         buf, size);
}
