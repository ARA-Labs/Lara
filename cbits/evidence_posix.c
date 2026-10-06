#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>

/* Explicit lengths make embedded NUL rejection independent of Haskell. */
static char *checked_path(const char *bytes, size_t length) {
  if (!length || memchr(bytes, 0, length)) { errno = EINVAL; return NULL; }
  char *path = malloc(length + 1);
  if (!path) return NULL;
  memcpy(path, bytes, length); path[length] = 0;
  return path;
}
int lara_evidence_root(const char *bytes, size_t length) {
  char *path = checked_path(bytes, length);
  if (!path) return -1;
  int fd = open(path, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
  int saved = errno; free(path); errno = saved; return fd;
}
int lara_evidence_open(int root, const char *bytes, size_t length) {
  char *path = checked_path(bytes, length);
  if (!path) return -1;
  if (path[0] == '/') { free(path); errno = EINVAL; return -1; }
  int dir = fcntl(root, F_DUPFD_CLOEXEC, 0), result = -1;
  if (dir < 0) { free(path); return -1; }
  char *component = path;
  for (;;) {
    char *slash = strchr(component, '/');
    if (slash) *slash = 0;
    if (!*component || !strcmp(component, ".") || !strcmp(component, "..")) { errno = EINVAL; break; }
    int flags = O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK;
    if (slash) flags |= O_DIRECTORY;
    int next = openat(dir, component, flags);
    if (next < 0) break;
    close(dir); dir = next;
    if (!slash) {
      struct stat st;
      if (fstat(dir, &st) < 0) break;
      if (!S_ISREG(st.st_mode)) { errno = EINVAL; break; }
      result = dir; dir = -1; break;
    }
    component = slash + 1;
  }
  int saved = errno; if (dir >= 0) close(dir); free(path); errno = saved;
  return result;
}
int lara_evidence_publish(const char *from, size_t from_length, const char *to, size_t to_length) {
  char *src = checked_path(from, from_length);
  if (!src) return -1;
  char *dst = checked_path(to, to_length);
  if (!dst) { int saved = errno; free(src); errno = saved; return -1; }
#ifdef SYS_renameat2
  int result = syscall(SYS_renameat2, AT_FDCWD, src, AT_FDCWD, dst, 1 /* RENAME_NOREPLACE */);
#else
  errno = ENOSYS;
  int result = -1;
#endif
  int saved = errno; free(src); free(dst); errno = saved; return result;
}
