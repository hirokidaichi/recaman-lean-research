#define _GNU_SOURCE

#include <dlfcn.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/*
 * The Work sandbox intentionally denies readlink("/proc/<pid>/exe").
 * Lean uses that call to locate its sysroot. This tiny preload shim supplies
 * the explicit executable path from LEAN_APP_PATH_OVERRIDE and delegates every
 * other readlink call to libc.
 */
ssize_t readlink(const char *path, char *buffer, size_t buffer_size) {
  const char *override = getenv("LEAN_APP_PATH_OVERRIDE");
  const size_t path_length = path == NULL ? 0 : strlen(path);
  const int is_proc_exe =
      path_length >= 10 && strncmp(path, "/proc/", 6) == 0 &&
      strcmp(path + path_length - 4, "/exe") == 0;

  if (override != NULL && is_proc_exe) {
    size_t length = strlen(override);
    if (length > buffer_size) {
      length = buffer_size;
    }
    memcpy(buffer, override, length);
    return (ssize_t)length;
  }

  static ssize_t (*real_readlink)(const char *, char *, size_t) = NULL;
  if (real_readlink == NULL) {
    real_readlink = dlsym(RTLD_NEXT, "readlink");
  }
  return real_readlink(path, buffer, buffer_size);
}
