/* main.c -- Mad Bullets .so loader
 *
 * Copyright (C) 2025 Rinnegatamante
 *
 * This software may be modified and distributed under the terms
 * of the MIT license.	See the LICENSE file for details.
 */

#include <vitasdk.h>
#include <kubridge.h>
#include <vitashark.h>
#include <vitaGL.h>
#include <zlib.h>
#include <zip.h>

#include <malloc.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <unistd.h>
#include <pthread.h>
#include <wchar.h>
#include <wctype.h>
#include <locale.h>
#include <setjmp.h>

#include <math.h>
#include <math_neon.h>

#include <errno.h>
#include <ctype.h>
#include <setjmp.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>

#include "main.h"
#include "config.h"
#include "dialog.h"
#include "so_util.h"
#include "sha1.h"

#define AL_ALEXT_PROTOTYPES
#include <AL/alext.h>
#include <AL/efx.h>

#include "vorbis/vorbisfile.h"

#include "libc_bridge.h"

//#define ENABLE_DEBUG

#ifdef ENABLE_DEBUG
#define dlog sceClibPrintf
#else
#define dlog
#endif

extern const char *BIONIC_ctype_;
extern const short *BIONIC_tolower_tab_;
extern const short *BIONIC_toupper_tab_;

static char data_path[256];

static char fake_vm[0x1000];
static char fake_env[0x1000];

int framecap = 0;

int file_exists(const char *path) {
	SceIoStat stat;
	return sceIoGetstat(path, &stat) >= 0;
}

int _newlib_heap_size_user = 160 * 1024 * 1024;
unsigned int sceLibcHeapSize = 4 * 1024 * 1024;

so_module main_mod;

void *__wrap_memcpy(void *dest, const void *src, size_t n) {
	return sceClibMemcpy(dest, src, n);
}

void *__wrap_memmove(void *dest, const void *src, size_t n) {
	return sceClibMemmove(dest, src, n);
}

int ret4() { return 4; }

void *__wrap_memset(void *s, int c, size_t n) {
	return sceClibMemset(s, c, n);
}

char *getcwd_hook(char *buf, size_t size) {
	strcpy(buf, data_path);
	return buf;
}

int posix_memalign(void **memptr, size_t alignment, size_t size) {
	*memptr = memalign(alignment, size);
	return 0;
}

int __android_log_print(int prio, const char *tag, const char *fmt, ...) {
#ifdef ENABLE_DEBUG
	va_list list;
	static char string[0x8000];

	va_start(list, fmt);
	vsprintf(string, fmt, list);
	va_end(list);

	sceClibPrintf("[LOG] %s: %s\n", tag, string);
#endif
	return 0;
}

int __android_log_write(int prio, const char *tag, const char *fmt, ...) {
#ifdef ENABLE_DEBUG
	va_list list;
	static char string[0x8000];

	va_start(list, fmt);
	vsprintf(string, fmt, list);
	va_end(list);

	sceClibPrintf("[LOGW] %s: %s\n", tag, string);
#endif
	return 0;
}

int __android_log_vprint(int prio, const char *tag, const char *fmt, va_list list) {
#ifdef ENABLE_DEBUG
	static char string[0x8000];

	vsprintf(string, fmt, list);
	va_end(list);

	sceClibPrintf("[LOGV] %s: %s\n", tag, string);
#endif
	return 0;
}

int ret0(void) {
	return 0;
}

int ret1(void) {
	return 1;
}

#define  MUTEX_TYPE_NORMAL	 0x0000
#define  MUTEX_TYPE_RECURSIVE  0x4000
#define  MUTEX_TYPE_ERRORCHECK 0x8000

static void init_static_mutex(pthread_mutex_t **mutex)
{
	pthread_mutex_t *mtxMem = NULL;

	switch ((int)*mutex) {
	case MUTEX_TYPE_NORMAL: {
		pthread_mutex_t initTmpNormal = PTHREAD_MUTEX_INITIALIZER;
		mtxMem = calloc(1, sizeof(pthread_mutex_t));
		sceClibMemcpy(mtxMem, &initTmpNormal, sizeof(pthread_mutex_t));
		*mutex = mtxMem;
		break;
	}
	case MUTEX_TYPE_RECURSIVE: {
		pthread_mutex_t initTmpRec = PTHREAD_RECURSIVE_MUTEX_INITIALIZER;
		mtxMem = calloc(1, sizeof(pthread_mutex_t));
		sceClibMemcpy(mtxMem, &initTmpRec, sizeof(pthread_mutex_t));
		*mutex = mtxMem;
		break;
	}
	case MUTEX_TYPE_ERRORCHECK: {
		pthread_mutex_t initTmpErr = PTHREAD_ERRORCHECK_MUTEX_INITIALIZER;
		mtxMem = calloc(1, sizeof(pthread_mutex_t));
		sceClibMemcpy(mtxMem, &initTmpErr, sizeof(pthread_mutex_t));
		*mutex = mtxMem;
		break;
	}
	default:
		break;
	}
}

static void init_static_cond(pthread_cond_t **cond)
{
	if (*cond == NULL) {
		pthread_cond_t initTmp = PTHREAD_COND_INITIALIZER;
		pthread_cond_t *condMem = calloc(1, sizeof(pthread_cond_t));
		sceClibMemcpy(condMem, &initTmp, sizeof(pthread_cond_t));
		*cond = condMem;
	}
}

int pthread_attr_destroy_soloader(pthread_attr_t **attr)
{
	int ret = pthread_attr_destroy(*attr);
	free(*attr);
	return ret;
}

int pthread_attr_getstack_soloader(const pthread_attr_t **attr,
				   void **stackaddr,
				   size_t *stacksize)
{
	return pthread_attr_getstack(*attr, stackaddr, stacksize);
}

__attribute__((unused)) int pthread_condattr_init_soloader(pthread_condattr_t **attr)
{
	*attr = calloc(1, sizeof(pthread_condattr_t));

	return pthread_condattr_init(*attr);
}

__attribute__((unused)) int pthread_condattr_destroy_soloader(pthread_condattr_t **attr)
{
	int ret = pthread_condattr_destroy(*attr);
	free(*attr);
	return ret;
}

int pthread_cond_init_soloader(pthread_cond_t **cond,
				   const pthread_condattr_t **attr)
{
	*cond = calloc(1, sizeof(pthread_cond_t));

	if (attr != NULL)
		return pthread_cond_init(*cond, *attr);
	else
		return pthread_cond_init(*cond, NULL);
}

int pthread_cond_destroy_soloader(pthread_cond_t **cond)
{
	int ret = pthread_cond_destroy(*cond);
	free(*cond);
	return ret;
}

int pthread_cond_signal_soloader(pthread_cond_t **cond)
{
	init_static_cond(cond);
	return pthread_cond_signal(*cond);
}

int pthread_cond_timedwait_soloader(pthread_cond_t **cond,
					pthread_mutex_t **mutex,
					struct timespec *abstime)
{
	init_static_cond(cond);
	init_static_mutex(mutex);
	return pthread_cond_timedwait(*cond, *mutex, abstime);
}

int pthread_create_soloader(pthread_t **thread,
				const pthread_attr_t **attr,
				void *(*start)(void *),
				void *param)
{
	*thread = calloc(1, sizeof(pthread_t));

	if (attr != NULL) {
		pthread_attr_setstacksize(*attr, 512 * 1024);
		return pthread_create(*thread, *attr, start, param);
	} else {
		pthread_attr_t attrr;
		pthread_attr_init(&attrr);
		pthread_attr_setstacksize(&attrr, 512 * 1024);
		return pthread_create(*thread, &attrr, start, param);
	}

}

int pthread_mutexattr_init_soloader(pthread_mutexattr_t **attr)
{
	*attr = calloc(1, sizeof(pthread_mutexattr_t));

	return pthread_mutexattr_init(*attr);
}

int pthread_mutexattr_settype_soloader(pthread_mutexattr_t **attr, int type)
{
	return pthread_mutexattr_settype(*attr, type);
}

int pthread_mutexattr_setpshared_soloader(pthread_mutexattr_t **attr, int pshared)
{
	return pthread_mutexattr_setpshared(*attr, pshared);
}

int pthread_mutexattr_destroy_soloader(pthread_mutexattr_t **attr)
{
	int ret = pthread_mutexattr_destroy(*attr);
	free(*attr);
	return ret;
}

int pthread_mutex_destroy_soloader(pthread_mutex_t **mutex)
{
	int ret = pthread_mutex_destroy(*mutex);
	free(*mutex);
	return ret;
}

int pthread_mutex_init_soloader(pthread_mutex_t **mutex,
				const pthread_mutexattr_t **attr)
{
	*mutex = calloc(1, sizeof(pthread_mutex_t));

	if (attr != NULL)
		return pthread_mutex_init(*mutex, *attr);
	else
		return pthread_mutex_init(*mutex, NULL);
}

int pthread_mutex_lock_soloader(pthread_mutex_t **mutex)
{
	init_static_mutex(mutex);
	return pthread_mutex_lock(*mutex);
}

int pthread_mutex_trylock_soloader(pthread_mutex_t **mutex)
{
	init_static_mutex(mutex);
	return pthread_mutex_trylock(*mutex);
}

int pthread_mutex_unlock_soloader(pthread_mutex_t **mutex)
{
	return pthread_mutex_unlock(*mutex);
}

int pthread_join_soloader(const pthread_t *thread, void **value_ptr)
{
	return pthread_join(*thread, value_ptr);
}

int pthread_cond_wait_soloader(pthread_cond_t **cond, pthread_mutex_t **mutex)
{
	return pthread_cond_wait(*cond, *mutex);
}

int pthread_cond_broadcast_soloader(pthread_cond_t **cond)
{
	return pthread_cond_broadcast(*cond);
}

int pthread_attr_init_soloader(pthread_attr_t **attr)
{
	*attr = calloc(1, sizeof(pthread_attr_t));

	return pthread_attr_init(*attr);
}

int pthread_attr_setdetachstate_soloader(pthread_attr_t **attr, int state)
{
	// pthread-embedded has JOINABLE/DETACHED swapped compared to BIONIC...
	return pthread_attr_setdetachstate(*attr, !state);
}

int pthread_attr_setstacksize_soloader(pthread_attr_t **attr, size_t stacksize)
{
	return pthread_attr_setstacksize(*attr, stacksize);
}

int pthread_attr_getstacksize_soloader(pthread_attr_t **attr, size_t *stacksize)
{
	return pthread_attr_getstacksize(*attr, stacksize);
}

int pthread_attr_setschedparam_soloader(pthread_attr_t **attr,
					const struct sched_param *param)
{
	return pthread_attr_setschedparam(*attr, param);
}

int pthread_attr_getschedparam_soloader(pthread_attr_t **attr,
					const struct sched_param *param)
{
	return pthread_attr_getschedparam(*attr, param);
}

int pthread_attr_setstack_soloader(pthread_attr_t **attr,
				   void *stackaddr,
				   size_t stacksize)
{
	return pthread_attr_setstack(*attr, stackaddr, stacksize);
}

int pthread_setschedparam_soloader(const pthread_t *thread, int policy,
				   const struct sched_param *param)
{
	return pthread_setschedparam(*thread, policy, param);
}

int pthread_getschedparam_soloader(const pthread_t *thread, int *policy,
				   struct sched_param *param)
{
	return pthread_getschedparam(*thread, policy, param);
}

int pthread_detach_soloader(const pthread_t *thread)
{
	return pthread_detach(*thread);
}

int pthread_getattr_np_soloader(pthread_t* thread, pthread_attr_t *attr) {
	fprintf(stderr, "[WARNING!] Not implemented: pthread_getattr_np\n");
	return 0;
}

int pthread_equal_soloader(const pthread_t *t1, const pthread_t *t2)
{
	if (t1 == t2)
		return 1;
	if (!t1 || !t2)
		return 0;
	return pthread_equal(*t1, *t2);
}

#ifndef MAX_TASK_COMM_LEN
#define MAX_TASK_COMM_LEN 16
#endif

int pthread_setname_np_soloader(const pthread_t *thread, const char* thread_name) {
	if (thread == 0 || thread_name == NULL) {
		return EINVAL;
	}
	size_t thread_name_len = strlen(thread_name);
	if (thread_name_len >= MAX_TASK_COMM_LEN) {
		return ERANGE;
	}

	// TODO: Implement the actual name setting if possible
	fprintf(stderr, "PTHR: pthread_setname_np with name %s\n", thread_name);

	return 0;
}

int clock_gettime_hook(int clk_id, struct timespec *t) {
	struct timeval now;
	int rv = gettimeofday(&now, NULL);
	if (rv)
		return rv;
	t->tv_sec = now.tv_sec;
	t->tv_nsec = now.tv_usec * 1000;

	return 0;
}


int GetCurrentThreadId(void) {
	return sceKernelGetThreadId();
}

extern void *__aeabi_uldivmod;
extern void *__aeabi_ldiv0;
extern void *__aeabi_ul2f;
extern void *__aeabi_l2f;
extern void *__aeabi_d2lz;
extern void *__aeabi_l2d;

int GetEnv(void *vm, void **env, int r2) {
	*env = fake_env;
	return 0;
}

void throw_exc(char **str, void *a, int b) {
	dlog("throwing %s\n", *str);
}

FILE *fopen_hook(char *fname, char *mode) {
	FILE *f;
	char real_fname[256];
	dlog("fopen(%s,%s)\n", fname, mode);
	if (strncmp(fname, "ux0:", 4)) {
		sprintf(real_fname, "ux0:data/bullets/%s", fname);
		dlog("fopen(%s,%s) patched\n", real_fname, mode);
		f = sceLibcBridge_fopen(real_fname, mode);
	} else {
		f = sceLibcBridge_fopen(fname, mode);
	}
	return f;
}

int open_hook(const char *fname, int flags, mode_t mode) {
	int f;
	char real_fname[256];
	dlog("open(%s)\n", fname);
	if (strncmp(fname, "ux0:", 4)) {
		sprintf(real_fname, "ux0:data/bullets/%s", fname);
		f = open(real_fname, flags, mode);
	} else {
		f = open(fname, flags, mode);
	}
	return f;
}

extern void *__aeabi_atexit;
extern void *__aeabi_ddiv;
extern void *__aeabi_dmul;
extern void *__aeabi_dadd;
extern void *__aeabi_i2d;
extern void *__aeabi_idiv;
extern void *__aeabi_idivmod;
extern void *__aeabi_ldivmod;
extern void *__aeabi_uidiv;
extern void *__aeabi_uidivmod;
extern void *__aeabi_uldivmod;
extern void *__cxa_atexit;
extern void *__cxa_finalize;
extern void *__cxa_call_unexpected;
extern void *__gnu_unwind_frame;
extern void *__stack_chk_fail;

static int __stack_chk_guard_fake = 0x42424242;

static FILE __sF_fake[0x1000][3];

typedef struct __attribute__((__packed__)) stat64_bionic {
	unsigned long long st_dev;
	unsigned char __pad0[4];
	unsigned long st_ino;
	unsigned int st_mode;
	unsigned int st_nlink;
	unsigned long st_uid;
	unsigned long st_gid;
	unsigned long long st_rdev;
	unsigned char __pad3[4];
	unsigned long st_size;
	unsigned long st_blksize;
	unsigned long st_blocks;
	unsigned long st_atime;
	unsigned long st_atime_nsec;
	unsigned long st_mtime;
	unsigned long st_mtime_nsec;
	unsigned long st_ctime;
	unsigned long st_ctime_nsec;
	unsigned long long __pad4;
} stat64_bionic;

int lstat_hook(const char *pathname, stat64_bionic *statbuf) {
	dlog("lstat(%s)\n", pathname);
	int res;
	struct stat st;
	if (strncmp(pathname, "ux0:", 4)) {
		char fname[256];
		sprintf(fname, "ux0:data/bullets/%s", pathname);
		dlog("lstat(%s) fixed\n", fname);
		res = stat(fname, &st);
	} else {
		res = stat(pathname, &st);
	}
	if (res == 0) {
		if (!statbuf) {
			statbuf = malloc(sizeof(stat64_bionic));
		}
		statbuf->st_dev = st.st_dev;
		statbuf->st_ino = st.st_ino;
		statbuf->st_mode = st.st_mode;
		statbuf->st_nlink = st.st_nlink;
		statbuf->st_uid = st.st_uid;
		statbuf->st_gid = st.st_gid;
		statbuf->st_rdev = st.st_rdev;
		statbuf->st_size = st.st_size;
		statbuf->st_blksize = st.st_blksize;
		statbuf->st_blocks = st.st_blocks;
		statbuf->st_atime = st.st_atime;
		statbuf->st_atime_nsec = 0;
		statbuf->st_mtime = st.st_mtime;
		statbuf->st_mtime_nsec = 0;
		statbuf->st_ctime = st.st_ctime;
		statbuf->st_ctime_nsec = 0;
	}
	return res;
}

int stat_hook(const char *pathname, stat64_bionic *statbuf) {
	dlog("stat(%s)\n", pathname);
	int res;
	struct stat st;
	if (strncmp(pathname, "ux0:", 4)) {
		char fname[256];
		sprintf(fname, "ux0:data/bullets/%s", pathname);
		dlog("stat(%s) fixed\n", fname);
		res = stat(fname, &st);
	} else {
		res = stat(pathname, &st);
	}
	if (res == 0) {
		if (!statbuf) {
			statbuf = malloc(sizeof(stat64_bionic));
		}
		statbuf->st_dev = st.st_dev;
		statbuf->st_ino = st.st_ino;
		statbuf->st_mode = st.st_mode;
		statbuf->st_nlink = st.st_nlink;
		statbuf->st_uid = st.st_uid;
		statbuf->st_gid = st.st_gid;
		statbuf->st_rdev = st.st_rdev;
		statbuf->st_size = st.st_size;
		statbuf->st_blksize = st.st_blksize;
		statbuf->st_blocks = st.st_blocks;
		statbuf->st_atime = st.st_atime;
		statbuf->st_atime_nsec = 0;
		statbuf->st_mtime = st.st_mtime;
		statbuf->st_mtime_nsec = 0;
		statbuf->st_ctime = st.st_ctime;
		statbuf->st_ctime_nsec = 0;
	}
	return res;
}

void *mmap(void *addr, size_t length, int prot, int flags, int fd, off_t offset) {
	return memalign(length, 0x1000);
}

int munmap(void *addr, size_t length) {
	free(addr);
	return 0;
}

int fstat_hook(int fd, void *statbuf) {
	struct stat st;
	int res = fstat(fd, &st);
	if (res == 0)
		*(uint64_t *)(statbuf + 0x30) = st.st_size;
	return res;
}

extern void *__cxa_guard_acquire;
extern void *__cxa_guard_release;

void *sceClibMemclr(void *dst, SceSize len) {
	if (!dst) {
		printf("memclr on NULL\n");
		return NULL;
	}
	return sceClibMemset(dst, 0, len);
}

void *sceClibMemset2(void *dst, SceSize len, int ch) {
	return sceClibMemset(dst, ch, len);
}

void *Android_JNI_GetEnv() {
	return fake_env;
}

void abort_hook() {
	dlog("abort called from %p\n", __builtin_return_address(0));
	uint8_t *p = NULL;
	p[0] = 1;
}

int ret99() {
	return 99;
}

int chdir_hook(const char *path) {
	return 0;
}

#define SCE_ERRNO_MASK 0xFF

#define DT_DIR 4
#define DT_REG 8

struct android_dirent {
	char pad[18];
	unsigned char d_type;
	char d_name[256];
};

typedef struct {
	SceUID uid;
	struct android_dirent dir;
} android_DIR;

int closedir_fake(android_DIR *dirp) {
	if (!dirp || dirp->uid < 0) {
		errno = EBADF;
		return -1;
	}

	int res = sceIoDclose(dirp->uid);
	dirp->uid = -1;

	free(dirp);

	if (res < 0) {
		errno = res & SCE_ERRNO_MASK;
		return -1;
	}

	errno = 0;
	return 0;
}

android_DIR *opendir_fake(const char *dirname) {
	dlog("opendir(%s)\n", dirname);
	SceUID uid;
	if (strncmp(dirname, "ux0:", 4)) {
		char real_fname[256];
		sprintf(real_fname, "ux0:data/bullets/%s", dirname);
		uid = sceIoDopen(real_fname);
	} else {
		uid = sceIoDopen(dirname);
	}
	
	if (uid < 0) {
		errno = uid & SCE_ERRNO_MASK;
		return NULL;
	}

	android_DIR *dirp = calloc(1, sizeof(android_DIR));

	if (!dirp) {
		sceIoDclose(uid);
		errno = ENOMEM;
		return NULL;
	}

	dirp->uid = uid;

	errno = 0;
	return dirp;
}

struct android_dirent *readdir_fake(android_DIR *dirp) {
	if (!dirp) {
		errno = EBADF;
		return NULL;
	}

	SceIoDirent sce_dir;
	int res = sceIoDread(dirp->uid, &sce_dir);

	if (res < 0) {
		errno = res & SCE_ERRNO_MASK;
		return NULL;
	}

	if (res == 0) {
		errno = 0;
		return NULL;
	}

	dirp->dir.d_type = SCE_S_ISDIR(sce_dir.d_stat.st_mode) ? DT_DIR : DT_REG;
	strcpy(dirp->dir.d_name, sce_dir.d_name);
	return &dirp->dir;
}

uint64_t lseek64(int fd, uint64_t offset, int whence) {
	return lseek(fd, offset, whence);
}

void __assert2(const char *file, int line, const char *func, const char *expr) {
	dlog("assertion failed:\n%s:%d (%s): %s\n", file, line, func, expr);
	sceKernelExitProcess(0);
}

void *dlsym_hook( void *handle, const char *symbol) {
	//dlog("dlsym %s\n", symbol);
	return vglGetProcAddress(symbol);
}

int strerror_r_hook(int errnum, char *buf, size_t buflen) {
	strerror_r(errnum, buf, buflen);
	dlog("Error %d: %s\n",errnum, buf);
	return 0;
}

extern void *__aeabi_ul2d;
extern void *__aeabi_d2ulz;

uint32_t fake_stdout;

int access_hook(const char *pathname, int mode) {
	dlog("access(%s)\n", pathname);
	if (strncmp(pathname, "ux0:", 4)) {
		char real_fname[256];
		sprintf(real_fname, "ux0:data/bullets/%s", pathname);
		return access(real_fname, mode);
	}
	
	return access(pathname, mode);
}

int mkdir_hook(const char *pathname, int mode) {
	dlog("mkdir(%s)\n", pathname);
	if (strncmp(pathname, "ux0:", 4)) {
		char real_fname[256];
		sprintf(real_fname, "ux0:data/bullets/%s", pathname);
		return mkdir(real_fname, mode);
	}
	
	return mkdir(pathname, mode);
}

FILE *AAssetManager_open(void *mgr, const char *fname, int mode) {
	char full_fname[256];
	sprintf(full_fname, "ux0:data/bullets/%s", fname);
	dlog("AAssetManager_open %s\n", full_fname);
	return sceLibcBridge_fopen(full_fname, "rb");
}

int AAsset_close(FILE *f) {
	return sceLibcBridge_fclose(f);
}

size_t AAsset_getLength(FILE *f) {
	size_t p = sceLibcBridge_ftell(f);
	sceLibcBridge_fseek(f, 0, SEEK_END);
	size_t res = sceLibcBridge_ftell(f);
	sceLibcBridge_fseek(f, p, SEEK_SET);
	return res;
}

size_t AAsset_read(FILE *f, void *buf, size_t count) {
	return sceLibcBridge_fread(buf, 1, count, f);
}

size_t AAsset_seek(FILE *f, size_t offs, int whence) {
	sceLibcBridge_fseek(f, offs, whence);
	return sceLibcBridge_ftell(f);
}

int rmdir_hook(const char *pathname) {
	dlog("rmdir(%s)\n", pathname);
	SceUID uid;
	if (strncmp(pathname, "ux0:", 4)) {
		char real_fname[256];
		sprintf(real_fname, "ux0:data/bullets/%s", pathname);
		return rmdir(real_fname);
	}
	
	return rmdir(pathname);
}

int unlink_hook(const char *pathname) {
	dlog("unlink(%s)\n", pathname);
	SceUID uid;
	if (strncmp(pathname, "ux0:", 4)) {
		char real_fname[256];
		sprintf(real_fname, "ux0:data/bullets/%s", pathname);
		return sceIoRemove(real_fname);
	}
	
	return sceIoRemove(pathname);
}

int remove_hook(const char *pathname) {
	dlog("unlink(%s)\n", pathname);
	SceUID uid;
	if (strncmp(pathname, "ux0:", 4)) {
		char real_fname[256];
		sprintf(real_fname, "ux0:data/bullets/%s", pathname);
		return sceIoRemove(real_fname);
	}
	
	return sceIoRemove(pathname);
}

DIR *AAssetManager_openDir(void *mgr, const char *fname) {
	dlog("AAssetManager_opendir(%s)\n", fname);
	if (strncmp(fname, "ux0:", 4)) {
		char real_fname[256];
		sprintf(real_fname, "ux0:data/bullets/%s", fname);
		return opendir(real_fname);
	}
	
	return opendir(fname);	
}

const char *AAssetDir_getNextFileName(DIR *assetDir) {
	struct dirent *ent;
	if (ent = readdir(assetDir)) {
		return ent->d_name;
	}
	return NULL;
}

void AAssetDir_close(DIR *assetDir) {
	closedir(assetDir);
}

int rename_hook(const char *old_filename, const char *new_filename) {
	dlog("rename %s -> %s\n", old_filename, new_filename);
	char real_old[256], real_new[256];
	if (strncmp(old_filename, "ux0:", 4)) {
		sprintf(real_old, "ux0:data/bullets/%s", old_filename);
	} else {
		strcpy(real_old, old_filename);
	}
	if (strncmp(new_filename, "ux0:", 4)) {
		sprintf(real_new, "ux0:data/bullets/%s", new_filename);
	} else {
		strcpy(real_new, new_filename);
	}
	return sceIoRename(real_old, real_new);
}

int nanosleep_hook(const struct timespec *req, struct timespec *rem) {
	const uint32_t usec = req->tv_sec * 1000 * 1000 + req->tv_nsec / 1000;
	return sceKernelDelayThreadCB(usec);
}

int sem_destroy_soloader(int * uid) {
    if (sceKernelDeleteSema(*uid) < 0)
        return -1;
    return 0;
}

int sem_getvalue_soloader (int * uid, int * sval) {
    SceKernelSemaInfo info;
    info.size = sizeof(SceKernelSemaInfo);

    if (sceKernelGetSemaInfo(*uid, &info) < 0) return -1;
    if (!sval) sval = malloc(sizeof(int32_t));
    *sval = info.currentCount;
    return 0;
}

int sem_init_soloader (int * uid, int pshared, unsigned int value) {
    *uid = sceKernelCreateSema("sema", 0, (int) value, 0x7fffffff, NULL);
    if (*uid < 0)
        return -1;
    return 0;
}

int sem_post_soloader (int * uid) {
    if (sceKernelSignalSema(*uid, 1) < 0)
        return -1;
    return 0;
}

uint64_t current_timestamp_ms() {
    struct timeval te;
    gettimeofday(&te, NULL);
    return (te.tv_sec*1000LL + te.tv_usec/1000);
}

int sem_timedwait_soloader (int * uid, const struct timespec * abstime) {
    uint timeout = 1000;
    if (sceKernelWaitSema(*uid, 1, &timeout) >= 0)
        return 0;
    if (!abstime) return -1;
    long long now = (long long) current_timestamp_ms() * 1000; // us
    long long _timeout = abstime->tv_sec * 1000 * 1000 + abstime->tv_nsec / 1000; // us
    if (_timeout-now >= 0) return -1;
    uint timeout_real = _timeout - now;
    if (sceKernelWaitSema(*uid, 1, &timeout_real) < 0)
        return -1;
    return 0;
}

int sem_trywait_soloader (int * uid) {
    uint timeout = 1000;
    if (sceKernelWaitSema(*uid, 1, &timeout) < 0)
        return -1;
    return 0;
}

int sem_wait_soloader (int * uid) {
    if (sceKernelWaitSema(*uid, 1, NULL) < 0)
        return -1;
    return 0;
}

extern void *__aeabi_memset8;
extern void *__aeabi_memset4;
extern void *__aeabi_memset;
extern void *__aeabi_memset8;
extern void *__aeabi_memcpy;
extern void *__aeabi_memcpy4;
extern void *__aeabi_memcpy8;
extern void *__aeabi_memclr;
extern void *__aeabi_memclr4;
extern void *__aeabi_memclr8;

size_t __strlen_chk(const char *s, size_t s_len) {
	return strlen(s);
}

int __vsprintf_chk(char* dest, int flags, size_t dest_len_from_compiler, const char *format, va_list va) {
	return vsprintf(dest, format, va);
}

void *__memmove_chk(void *dest, const void *src, size_t len, size_t dstlen) {
	return memmove(dest, src, len);
}

void *__memset_chk(void *dest, int val, size_t len, size_t dstlen) {
	return memset(dest, val, len);
}

size_t __strlcat_chk (char *dest, char *src, size_t len, size_t dstlen) {
	return strlcat(dest, src, len);
}

size_t __strlcpy_chk (char *dest, char *src, size_t len, size_t dstlen) {
	return strlcpy(dest, src, len);
}

char* __strchr_chk(const char* p, int ch, size_t s_len) {
	return strchr(p, ch);
}

char *__strcat_chk(char *dest, const char *src, size_t destlen) {
	return strcat(dest, src);
}

char *__strrchr_chk(const char *p, int ch, size_t s_len) {
	return strrchr(p, ch);
}

char *__strcpy_chk(char *dest, const char *src, size_t destlen) {
	return strcpy(dest, src);
}

char *__strncat_chk(char *s1, const char *s2, size_t n, size_t s1len) {
	return strncat(s1, s2, n);
}

void *__memcpy_chk(void *dest, const void *src, size_t len, size_t destlen) {
	return memcpy(dest, src, len);
}

int __vsnprintf_chk(char *s, size_t maxlen, int flag, size_t slen, const char *format, va_list args) {
	return vsnprintf(s, maxlen, format, args);
}

void *malloc_hook(size_t sz) {
	return memalign(16, sz);
}

int sceLibcBridge_fseeko(FILE *stream, off_t offset, int origin) {
	return sceLibcBridge_fseek(stream, offset, origin);
}

off_t sceLibcBridge_ftello(FILE *stream) {
	return sceLibcBridge_ftell(stream);
}

static so_default_dynlib default_dynlib[] = {
	{ "__memcpy_chk", (uintptr_t)&__memcpy_chk },
	{ "__memmove_chk", (uintptr_t)&__memmove_chk },
	{ "__memset_chk", (uintptr_t)&__memset_chk },
	{ "__strcat_chk", (uintptr_t)&__strcat_chk },
	{ "__strchr_chk", (uintptr_t)&__strchr_chk },
	{ "__strcpy_chk", (uintptr_t)&__strcpy_chk },
	{ "__strlcat_chk", (uintptr_t)&__strlcat_chk },
	{ "__strlcpy_chk", (uintptr_t)&__strlcpy_chk },
	{ "__strlen_chk", (uintptr_t)&__strlen_chk },
	{ "__strncat_chk", (uintptr_t)&__strncat_chk },
	{ "__strrchr_chk", (uintptr_t)&__strrchr_chk },
	{ "__vsprintf_chk", (uintptr_t)&__vsprintf_chk },
	{ "__vsnprintf_chk", (uintptr_t)&__vsnprintf_chk },
	{ "fmaxf", (uintptr_t)&fmaxf },
	{ "fmaf", (uintptr_t)&fmaf },
	{ "fminf", (uintptr_t)&fminf },
	{ "ftruncate", (uintptr_t)&ftruncate },
	{ "pthread_setname_np", (uintptr_t)&ret0 },
	{ "memrchr", (uintptr_t)&memrchr },
	{ "strtok_r", (uintptr_t)&strtok_r },
	{ "glGenRenderbuffers", (uintptr_t)&ret0 },
	{ "glRenderbufferStorage", (uintptr_t)&ret0 },
	{ "glFramebufferRenderbuffer", (uintptr_t)&ret0 },
	{ "glDeleteRenderbuffers", (uintptr_t)&ret0 },
	{ "glBindRenderbuffer", (uintptr_t)&ret0 },
	{ "fsetpos", (uintptr_t)&fsetpos },
	{ "sem_destroy", (uintptr_t)&sem_destroy_soloader },
	{ "sem_getvalue", (uintptr_t)&sem_getvalue_soloader },
	{ "sem_init", (uintptr_t)&sem_init_soloader },
	{ "sem_post", (uintptr_t)&sem_post_soloader },
	{ "sem_timedwait", (uintptr_t)&sem_timedwait_soloader },
	{ "sem_trywait", (uintptr_t)&sem_trywait_soloader },
	{ "sem_wait", (uintptr_t)&sem_wait_soloader },
	{ "alIsExtensionPresent", (uintptr_t)&alIsExtensionPresent },
	{ "alBufferData", (uintptr_t)&alBufferData },
	{ "alDeleteBuffers", (uintptr_t)&alDeleteBuffers },
	{ "alDeleteSources", (uintptr_t)&alDeleteSources },
	{ "alDistanceModel", (uintptr_t)&alDistanceModel },
	{ "alGenBuffers", (uintptr_t)&alGenBuffers },
	{ "alGenSources", (uintptr_t)&alGenSources },
	{ "alGetProcAddress", (uintptr_t)&alGetProcAddress },
	{ "alSpeedOfSound", (uintptr_t)&alSpeedOfSound },
	{ "alDopplerFactor", (uintptr_t)&alDopplerFactor },
	{ "alcIsExtensionPresent", (uintptr_t)&alcIsExtensionPresent },
	{ "alcGetCurrentContext", (uintptr_t)&alcGetCurrentContext },
	{ "alGetBufferi", (uintptr_t)&alGetBufferi },
	{ "alGetError", (uintptr_t)&alGetError },
	{ "alGetString", (uintptr_t)&alGetString },
	{ "alSource3i", (uintptr_t)&alSource3i },
	{ "alSourcefv", (uintptr_t)&alSourcefv },
	{ "alIsSource", (uintptr_t)&alIsSource },
	{ "alGetSourcei", (uintptr_t)&alGetSourcei },
	{ "alGetSourcef", (uintptr_t)&alGetSourcef },
	{ "alIsBuffer", (uintptr_t)&alIsBuffer },
	{ "alListener3f", (uintptr_t)&alListener3f },
	{ "alListenerf", (uintptr_t)&alListenerf },
	{ "alListenerfv", (uintptr_t)&alListenerfv },
	{ "alSource3f", (uintptr_t)&alSource3f },
	{ "alSourcePause", (uintptr_t)&alSourcePause },
	{ "alSourcePlay", (uintptr_t)&alSourcePlay },
	{ "alSourceQueueBuffers", (uintptr_t)&alSourceQueueBuffers },
	{ "alSourceStop", (uintptr_t)&alSourceStop },
	{ "alSourceRewind", (uintptr_t)&alSourceRewind },
	{ "alSourceUnqueueBuffers", (uintptr_t)&alSourceUnqueueBuffers },
	{ "alSourcef", (uintptr_t)&alSourcef },
	{ "alSourcei", (uintptr_t)&alSourcei },
	{ "alcCaptureSamples", (uintptr_t)&alcCaptureSamples },
	{ "alcCaptureStart", (uintptr_t)&alcCaptureStart },
	{ "alcCaptureStop", (uintptr_t)&alcCaptureStop },
	{ "alcCaptureOpenDevice", (uintptr_t)&alcCaptureOpenDevice },
	{ "alcCloseDevice", (uintptr_t)&alcCloseDevice },
	{ "alcCreateContext", (uintptr_t)&alcCreateContext },
	{ "alcGetContextsDevice", (uintptr_t)&alcGetContextsDevice },
	{ "alcGetError", (uintptr_t)&alcGetError },
	{ "alcGetIntegerv", (uintptr_t)&alcGetIntegerv },
	{ "alcGetString", (uintptr_t)&ret0 }, // FIXME
	{ "alcMakeContextCurrent", (uintptr_t)&alcMakeContextCurrent },
	{ "alcDestroyContext", (uintptr_t)&alcDestroyContext },
	{ "alcOpenDevice", (uintptr_t)&alcOpenDevice },
	{ "alcProcessContext", (uintptr_t)&alcProcessContext },
	{ "alcPauseCurrentDevice", (uintptr_t)&ret0 },
	{ "alcResumeCurrentDevice", (uintptr_t)&ret0 },
	{ "alcSuspendContext", (uintptr_t)&alcSuspendContext },
	{ "rename", (uintptr_t)&rename_hook},
	{ "glGetError", (uintptr_t)&ret0},
	{ "glValidateProgram", (uintptr_t)&ret0},
	{ "strtoll_l", (uintptr_t)&strtoll_l},
	{ "strtoull_l", (uintptr_t)&strtoull_l},
	{ "strtold_l", (uintptr_t)&strtold_l},
	{ "wcstoul", (uintptr_t)&wcstoul},
	{ "wcstoll", (uintptr_t)&wcstoll},
	{ "wcstoull", (uintptr_t)&wcstoull},
	{ "wcstof", (uintptr_t)&wcstof},
	{ "wcstod", (uintptr_t)&wcstod},
	{ "wcsnrtombs", (uintptr_t)&wcsnrtombs},
	{ "mbsnrtowcs", (uintptr_t)&mbsnrtowcs},
	{ "mbtowc", (uintptr_t)&mbtowc},
	{ "mbrlen", (uintptr_t)&mbrlen},
	{ "isblank", (uintptr_t)&isblank},
	{ "rmdir", (uintptr_t)&rmdir_hook},
	{ "AAssetManager_openDir", (uintptr_t)&AAssetManager_openDir},
	{ "AAssetDir_getNextFileName", (uintptr_t)&AAssetDir_getNextFileName},
	{ "AAssetDir_close", (uintptr_t)&AAssetDir_close},
	{ "rmdir", (uintptr_t)&rmdir_hook},
	{ "_setjmp", (uintptr_t)&setjmp},
	{ "_longjmp", (uintptr_t)&longjmp},
	{ "glFramebufferTexture2D", (uintptr_t)&glFramebufferTexture2D},
	{ "AAssetManager_open", (uintptr_t)&AAssetManager_open},
	{ "AAsset_close", (uintptr_t)&AAsset_close},
	{ "AAssetManager_fromJava", (uintptr_t)&ret1},
	{ "AAsset_read", (uintptr_t)&AAsset_read},
	{ "AAsset_seek", (uintptr_t)&AAsset_seek},
	{ "AAsset_getLength", (uintptr_t)&AAsset_getLength},
	{ "stdout", (uintptr_t)&fake_stdout },
	{ "stdin", (uintptr_t)&fake_stdout },
	{ "stderr", (uintptr_t)&fake_stdout },
	{ "newlocale", (uintptr_t)&newlocale },
	{ "uselocale", (uintptr_t)&uselocale },
	{ "ov_read", (uintptr_t)&ov_read },
	{ "ov_raw_seek", (uintptr_t)&ov_raw_seek },
	{ "ov_open_callbacks", (uintptr_t)&ov_open_callbacks },
	{ "ov_pcm_total", (uintptr_t)&ov_pcm_total },
	{ "ov_clear", (uintptr_t)&ov_clear },
	{ "exp2f", (uintptr_t)&exp2f },
	{ "__aeabi_l2d", (uintptr_t)&__aeabi_l2d },
	{ "__aeabi_d2ulz", (uintptr_t)&__aeabi_d2ulz },
	{ "__aeabi_ul2d", (uintptr_t)&__aeabi_ul2d },
	{ "__pthread_cleanup_push", (uintptr_t)&ret0 },
	{ "__pthread_cleanup_pop", (uintptr_t)&ret0 },
	{ "sincos", (uintptr_t)&sincos },
	{ "__assert2", (uintptr_t)&__assert2 },
	{ "glTexParameteri", (uintptr_t)&glTexParameteri},
	{ "glReadPixels", (uintptr_t)&glReadPixels},
	{ "glShaderSource", (uintptr_t)&glShaderSource},
	{ "sincosf", (uintptr_t)&sincosf },
	{ "opendir", (uintptr_t)&opendir_fake },
	{ "readdir", (uintptr_t)&readdir_fake },
	{ "closedir", (uintptr_t)&closedir_fake },
	{ "__aeabi_ul2f", (uintptr_t)&__aeabi_ul2f },
	{ "__aeabi_l2f", (uintptr_t)&__aeabi_l2f },
	{ "__aeabi_d2lz", (uintptr_t)&__aeabi_d2lz },
	{ "__aeabi_uldivmod", (uintptr_t)&__aeabi_uldivmod },
	{ "__aeabi_memclr", (uintptr_t)&__aeabi_memclr },
	{ "__aeabi_memclr4", (uintptr_t)&__aeabi_memclr4 },
	{ "__aeabi_memclr8", (uintptr_t)&__aeabi_memclr8 },
	{ "__aeabi_memcpy4", (uintptr_t)&__aeabi_memcpy4 },
	{ "__aeabi_memcpy8", (uintptr_t)&__aeabi_memcpy8 },
	{ "__aeabi_memmove4", (uintptr_t)&memmove },
	{ "__aeabi_memmove8", (uintptr_t)&memmove },
	{ "__aeabi_memcpy", (uintptr_t)&__aeabi_memcpy },
	{ "__aeabi_memmove", (uintptr_t)&memmove },
	{ "__aeabi_memset", (uintptr_t)&__aeabi_memset },
	{ "__aeabi_memset4", (uintptr_t)&__aeabi_memset4 },
	{ "__aeabi_memset8", (uintptr_t)&__aeabi_memset8 },
	{ "__aeabi_atexit", (uintptr_t)&__aeabi_atexit },
	{ "__aeabi_uidiv", (uintptr_t)&__aeabi_uidiv },
	{ "__aeabi_uidivmod", (uintptr_t)&__aeabi_uidivmod },
	{ "__aeabi_ldivmod", (uintptr_t)&__aeabi_ldivmod },
	{ "__aeabi_idivmod", (uintptr_t)&__aeabi_idivmod },
	{ "__aeabi_idiv", (uintptr_t)&__aeabi_idiv },
	{ "__aeabi_ddiv", (uintptr_t)&__aeabi_ddiv },
	{ "__aeabi_dmul", (uintptr_t)&__aeabi_dmul },
	{ "__aeabi_dadd", (uintptr_t)&__aeabi_dadd },
	{ "__aeabi_i2d", (uintptr_t)&__aeabi_i2d },
	{ "__android_log_print", (uintptr_t)&__android_log_print },
	{ "__android_log_vprint", (uintptr_t)&__android_log_vprint },
	{ "__android_log_write", (uintptr_t)&__android_log_write },
	{ "__cxa_atexit", (uintptr_t)&__cxa_atexit },
	{ "__cxa_call_unexpected", (uintptr_t)&__cxa_call_unexpected },
	{ "__cxa_guard_acquire", (uintptr_t)&__cxa_guard_acquire },
	{ "__cxa_guard_release", (uintptr_t)&__cxa_guard_release },
	{ "__cxa_finalize", (uintptr_t)&__cxa_finalize },
	{ "__errno", (uintptr_t)&__errno },
	{ "__gnu_unwind_frame", (uintptr_t)&__gnu_unwind_frame },
	{ "__gnu_Unwind_Find_exidx", (uintptr_t)&ret0 },
	{ "dl_unwind_find_exidx", (uintptr_t)&ret0 },
	{ "__sF", (uintptr_t)&__sF_fake },
	{ "__stack_chk_fail", (uintptr_t)&__stack_chk_fail },
	{ "__stack_chk_guard", (uintptr_t)&__stack_chk_guard_fake },
	{ "_ctype_", (uintptr_t)&BIONIC_ctype_},
	{ "_tolower_tab_", (uintptr_t)&BIONIC_tolower_tab_},
	{ "_toupper_tab_", (uintptr_t)&BIONIC_toupper_tab_},
	{ "abort", (uintptr_t)&abort_hook },
	{ "access", (uintptr_t)&access_hook },
	{ "acos", (uintptr_t)&acos },
	{ "acosh", (uintptr_t)&acosh },
	{ "asctime", (uintptr_t)&asctime },
	{ "acosf", (uintptr_t)&acosf },
	{ "asin", (uintptr_t)&asin },
	{ "asinh", (uintptr_t)&asinh },
	{ "asinf", (uintptr_t)&asinf },
	{ "atan", (uintptr_t)&atan },
	{ "atanh", (uintptr_t)&atanh },
	{ "atan2", (uintptr_t)&atan2 },
	{ "atan2f", (uintptr_t)&atan2f },
	{ "atanf", (uintptr_t)&atanf },
	{ "atoi", (uintptr_t)&atoi },
	{ "atol", (uintptr_t)&atol },
	{ "atoll", (uintptr_t)&atoll },
	{ "basename", (uintptr_t)&basename },
	// { "bind", (uintptr_t)&bind },
	{ "bsd_signal", (uintptr_t)&ret0 },
	{ "bsearch", (uintptr_t)&bsearch },
	{ "btowc", (uintptr_t)&btowc },
	{ "calloc", (uintptr_t)&calloc },
	{ "ceil", (uintptr_t)&ceil },
	{ "ceilf", (uintptr_t)&ceilf },
	{ "chdir", (uintptr_t)&chdir_hook },
	{ "clearerr", (uintptr_t)&clearerr },
	{ "clock", (uintptr_t)&clock },
	{ "clock_gettime", (uintptr_t)&clock_gettime_hook },
	{ "close", (uintptr_t)&close },
	{ "cos", (uintptr_t)&cos },
	{ "cosf", (uintptr_t)&cosf },
	{ "cosh", (uintptr_t)&cosh },
	{ "crc32", (uintptr_t)&crc32 },
	{ "deflate", (uintptr_t)&deflate },
	{ "deflateEnd", (uintptr_t)&deflateEnd },
	{ "deflateInit_", (uintptr_t)&deflateInit_ },
	{ "deflateInit2_", (uintptr_t)&deflateInit2_ },
	{ "deflateReset", (uintptr_t)&deflateReset },
	{ "difftime", (uintptr_t)&difftime },
	{ "dlopen", (uintptr_t)&ret0 },
	{ "dlsym", (uintptr_t)&dlsym_hook },
	{ "exit", (uintptr_t)&exit },
	{ "exp", (uintptr_t)&exp },
	{ "exp2", (uintptr_t)&exp2 },
	{ "expf", (uintptr_t)&expf },
	{ "fabsf", (uintptr_t)&fabsf },
	{ "fclose", (uintptr_t)&sceLibcBridge_fclose },
	{ "fcntl", (uintptr_t)&ret0 },
	{ "mktime", (uintptr_t)&mktime },
	// { "fdopen", (uintptr_t)&fdopen },
	{ "feof", (uintptr_t)&sceLibcBridge_feof },
	{ "ferror", (uintptr_t)&sceLibcBridge_ferror },
	{ "fflush", (uintptr_t)&ret0 },
	{ "fgetc", (uintptr_t)&sceLibcBridge_fgetc },
	{ "fgets", (uintptr_t)&sceLibcBridge_fgets },
	{ "floor", (uintptr_t)&floor },
	{ "fileno", (uintptr_t)&fileno },
	{ "floorf", (uintptr_t)&floorf },
	{ "fmod", (uintptr_t)&fmod },
	{ "fmodf", (uintptr_t)&fmodf },
	{ "funopen", (uintptr_t)&funopen },
	{ "fopen", (uintptr_t)&fopen_hook },
	{ "open", (uintptr_t)&open_hook },
	{ "fprintf", (uintptr_t)&sceLibcBridge_fprintf },
	{ "fputc", (uintptr_t)&sceLibcBridge_fputc },
	// { "fputwc", (uintptr_t)&fputwc },
	{ "fputs", (uintptr_t)&sceLibcBridge_fputs },
	{ "fread", (uintptr_t)&sceLibcBridge_fread },
	{ "free", (uintptr_t)&free },
	{ "frexp", (uintptr_t)&frexp },
	{ "frexpf", (uintptr_t)&frexpf },
	{ "fscanf", (uintptr_t)&fscanf },
	{ "fseek", (uintptr_t)&sceLibcBridge_fseek },
	{ "fseeko", (uintptr_t)&sceLibcBridge_fseeko },
	// { "fstat", (uintptr_t)&fstat_hook },
	{ "ftell", (uintptr_t)&sceLibcBridge_ftell },
	{ "ftello", (uintptr_t)&sceLibcBridge_ftello },
	// { "ftruncate", (uintptr_t)&ftruncate },
	{ "fwrite", (uintptr_t)&sceLibcBridge_fwrite },
	{ "getc", (uintptr_t)&sceLibcBridge_getc },
	{ "gettid", (uintptr_t)&ret0 },
	{ "getpid", (uintptr_t)&ret0 },
	{ "getcwd", (uintptr_t)&getcwd_hook },
	{ "getenv", (uintptr_t)&ret0 },
	{ "getwc", (uintptr_t)&getwc },
	{ "gettimeofday", (uintptr_t)&gettimeofday },
	{ "gzopen", (uintptr_t)&gzopen },
	{ "inflate", (uintptr_t)&inflate },
	{ "inflateEnd", (uintptr_t)&inflateEnd },
	{ "inflateInit_", (uintptr_t)&inflateInit_ },
	{ "inflateInit2_", (uintptr_t)&inflateInit2_ },
	{ "inflateReset", (uintptr_t)&inflateReset },
	{ "isascii", (uintptr_t)&isascii },
	{ "isalnum", (uintptr_t)&isalnum },
	{ "isalpha", (uintptr_t)&isalpha },
	{ "iscntrl", (uintptr_t)&iscntrl },
	{ "isdigit", (uintptr_t)&isdigit },
	{ "islower", (uintptr_t)&islower },
	{ "ispunct", (uintptr_t)&ispunct },
	{ "isprint", (uintptr_t)&isprint },
	{ "isspace", (uintptr_t)&isspace },
	{ "isupper", (uintptr_t)&isupper },
	{ "iswalpha", (uintptr_t)&iswalpha },
	{ "iswcntrl", (uintptr_t)&iswcntrl },
	{ "iswctype", (uintptr_t)&iswctype },
	{ "iswdigit", (uintptr_t)&iswdigit },
	{ "iswdigit", (uintptr_t)&iswdigit },
	{ "iswlower", (uintptr_t)&iswlower },
	{ "iswprint", (uintptr_t)&iswprint },
	{ "iswpunct", (uintptr_t)&iswpunct },
	{ "iswspace", (uintptr_t)&iswspace },
	{ "iswupper", (uintptr_t)&iswupper },
	{ "iswxdigit", (uintptr_t)&iswxdigit },
	{ "isxdigit", (uintptr_t)&isxdigit },
	{ "ldexp", (uintptr_t)&ldexp },
	{ "ldexpf", (uintptr_t)&ldexpf },
	// { "listen", (uintptr_t)&listen },
	{ "localtime", (uintptr_t)&localtime },
	{ "localtime_r", (uintptr_t)&localtime_r },
	{ "log", (uintptr_t)&log },
	{ "logf", (uintptr_t)&logf },
	{ "log10", (uintptr_t)&log10 },
	{ "log10f", (uintptr_t)&log10f },
	{ "longjmp", (uintptr_t)&longjmp },
	{ "lrand48", (uintptr_t)&lrand48 },
	{ "lrint", (uintptr_t)&lrint },
	{ "lrintf", (uintptr_t)&lrintf },
	{ "lseek", (uintptr_t)&lseek },
	{ "lseek64", (uintptr_t)&lseek64 },
	{ "malloc", (uintptr_t)&malloc_hook },
	{ "mbrtowc", (uintptr_t)&mbrtowc },
	{ "memalign", (uintptr_t)&memalign },
	{ "memchr", (uintptr_t)&sceClibMemchr },
	{ "memcmp", (uintptr_t)&memcmp },
	{ "memcpy", (uintptr_t)&sceClibMemcpy },
	{ "memmove", (uintptr_t)&memmove },
	{ "memset", (uintptr_t)&sceClibMemset },
	{ "mkdir", (uintptr_t)&mkdir_hook },
	// { "mmap", (uintptr_t)&mmap},
	// { "munmap", (uintptr_t)&munmap},
	{ "modf", (uintptr_t)&modf },
	{ "modff", (uintptr_t)&modff },
	// { "poll", (uintptr_t)&poll },
	{ "pow", (uintptr_t)&pow },
	{ "powf", (uintptr_t)&powf },
	{ "printf", (uintptr_t)&printf },
	{ "pthread_join", (uintptr_t)&pthread_join_soloader },
	{ "pthread_attr_destroy", (uintptr_t)&pthread_attr_destroy_soloader },
	{ "pthread_attr_getstack", (uintptr_t)&pthread_attr_getstack_soloader },
	{ "pthread_attr_init", (uintptr_t) &pthread_attr_init_soloader },
	{ "pthread_attr_setdetachstate", (uintptr_t) &pthread_attr_setdetachstate_soloader },
	{ "pthread_attr_setschedparam", (uintptr_t)&pthread_attr_setschedparam_soloader },
	{ "pthread_attr_getschedparam", (uintptr_t)&pthread_attr_getschedparam_soloader },
	{ "pthread_attr_setschedpolicy", (uintptr_t)&ret0 },
	{ "pthread_attr_setstack", (uintptr_t)&pthread_attr_setstack_soloader },
	{ "pthread_attr_setstacksize", (uintptr_t) &pthread_attr_setstacksize_soloader },
	{ "pthread_attr_getstacksize", (uintptr_t) &pthread_attr_getstacksize_soloader },
	{ "pthread_cond_broadcast", (uintptr_t) &pthread_cond_broadcast_soloader },
	{ "pthread_cond_destroy", (uintptr_t) &pthread_cond_destroy_soloader },
	{ "pthread_cond_init", (uintptr_t) &pthread_cond_init_soloader },
	{ "pthread_cond_signal", (uintptr_t) &pthread_cond_signal_soloader },
	{ "pthread_cond_timedwait", (uintptr_t) &pthread_cond_timedwait_soloader },
	{ "pthread_cond_wait", (uintptr_t) &pthread_cond_wait_soloader },
	{ "pthread_condattr_init", (uintptr_t) &pthread_condattr_init_soloader },
	{ "pthread_condattr_destroy", (uintptr_t) &pthread_condattr_destroy_soloader },
	{ "pthread_create", (uintptr_t) &pthread_create_soloader },
	{ "pthread_detach", (uintptr_t) &pthread_detach_soloader },
	{ "pthread_equal", (uintptr_t) &pthread_equal_soloader },
	{ "pthread_exit", (uintptr_t) &pthread_exit },
	{ "pthread_getattr_np", (uintptr_t) &pthread_getattr_np_soloader },
	{ "pthread_getschedparam", (uintptr_t) &pthread_getschedparam_soloader },
	{ "pthread_getspecific", (uintptr_t)&pthread_getspecific },
	{ "pthread_key_create", (uintptr_t)&pthread_key_create },
	{ "pthread_key_delete", (uintptr_t)&pthread_key_delete },
	{ "pthread_mutex_destroy", (uintptr_t) &pthread_mutex_destroy_soloader },
	{ "pthread_mutex_init", (uintptr_t) &pthread_mutex_init_soloader },
	{ "pthread_mutex_lock", (uintptr_t) &pthread_mutex_lock_soloader },
	{ "pthread_mutex_trylock", (uintptr_t) &pthread_mutex_trylock_soloader},
	{ "pthread_mutex_unlock", (uintptr_t) &pthread_mutex_unlock_soloader },
	{ "pthread_mutexattr_destroy", (uintptr_t) &pthread_mutexattr_destroy_soloader},
	{ "pthread_mutexattr_init", (uintptr_t) &pthread_mutexattr_init_soloader},
	{ "pthread_mutexattr_setpshared", (uintptr_t) &pthread_mutexattr_setpshared_soloader},
	{ "pthread_mutexattr_settype", (uintptr_t) &pthread_mutexattr_settype_soloader},
	{ "pthread_once", (uintptr_t)&pthread_once },
	{ "pthread_self", (uintptr_t) &pthread_self },
	{ "pthread_setschedparam", (uintptr_t) &pthread_setschedparam_soloader },
	{ "pthread_setspecific", (uintptr_t)&pthread_setspecific },
	{ "sched_get_priority_min", (uintptr_t)&ret0 },
	{ "sched_get_priority_max", (uintptr_t)&ret99 },
	{ "putc", (uintptr_t)&putc },
	{ "puts", (uintptr_t)&puts },
	{ "putwc", (uintptr_t)&putwc },
	{ "qsort", (uintptr_t)&qsort },
	{ "rand", (uintptr_t)&rand },
	{ "read", (uintptr_t)&read },
	{ "realpath", (uintptr_t)&realpath },
	{ "realloc", (uintptr_t)&realloc },
	// { "recv", (uintptr_t)&recv },
	{ "roundf", (uintptr_t)&roundf },
	{ "rint", (uintptr_t)&rint },
	{ "rintf", (uintptr_t)&rintf },
	// { "send", (uintptr_t)&send },
	// { "sendto", (uintptr_t)&sendto },
	{ "setenv", (uintptr_t)&ret0 },
	{ "setjmp", (uintptr_t)&setjmp },
	{ "setlocale", (uintptr_t)&ret0 },
	// { "setsockopt", (uintptr_t)&setsockopt },
	{ "setvbuf", (uintptr_t)&setvbuf },
	{ "sin", (uintptr_t)&sin },
	{ "sinf", (uintptr_t)&sinf },
	{ "sinh", (uintptr_t)&sinh },
	//{ "sincos", (uintptr_t)&sincos },
	{ "snprintf", (uintptr_t)&snprintf },
	// { "socket", (uintptr_t)&socket },
	{ "sprintf", (uintptr_t)&sprintf },
	{ "sqrt", (uintptr_t)&sqrt },
	{ "sqrtf", (uintptr_t)&sqrtf },
	{ "srand", (uintptr_t)&srand },
	{ "srand48", (uintptr_t)&srand48 },
	{ "sscanf", (uintptr_t)&sscanf },
	{ "stat", (uintptr_t)&stat_hook },
	{ "lstat", (uintptr_t)&lstat_hook },
	{ "strcasecmp", (uintptr_t)&strcasecmp },
	{ "strcasestr", (uintptr_t)&strstr },
	{ "strcat", (uintptr_t)&strcat },
	{ "strchr", (uintptr_t)&strchr },
	{ "strcmp", (uintptr_t)&strcmp },
	{ "strcoll", (uintptr_t)&strcoll },
	{ "strcpy", (uintptr_t)&strcpy },
	{ "strcspn", (uintptr_t)&strcspn },
	{ "strdup", (uintptr_t)&strdup },
	{ "strerror", (uintptr_t)&strerror },
	{ "strerror_r", (uintptr_t)&strerror_r_hook },
	{ "strftime", (uintptr_t)&strftime },
	{ "strlcpy", (uintptr_t)&strlcpy },
	{ "strlen", (uintptr_t)&strlen },
	{ "strncasecmp", (uintptr_t)&strncasecmp },
	{ "strncat", (uintptr_t)&strncat },
	{ "strncmp", (uintptr_t)&strncmp },
	{ "strncpy", (uintptr_t)&strncpy },
	{ "strpbrk", (uintptr_t)&strpbrk },
	{ "strrchr", (uintptr_t)&strrchr },
	{ "strstr", (uintptr_t)&strstr },
	{ "strtod", (uintptr_t)&strtod },
	{ "strtol", (uintptr_t)&strtol },
	{ "strtoul", (uintptr_t)&strtoul },
	{ "strtoll", (uintptr_t)&strtoll },
	{ "strtoull", (uintptr_t)&strtoull },
	{ "strtok", (uintptr_t)&strtok },
	{ "strxfrm", (uintptr_t)&strxfrm },
	{ "sysconf", (uintptr_t)&ret0 },
	{ "tan", (uintptr_t)&tan },
	{ "tanf", (uintptr_t)&tanf },
	{ "tanh", (uintptr_t)&tanh },
	{ "time", (uintptr_t)&time },
	{ "tolower", (uintptr_t)&tolower },
	{ "toupper", (uintptr_t)&toupper },
	{ "towlower", (uintptr_t)&towlower },
	{ "towupper", (uintptr_t)&towupper },
	{ "ungetc", (uintptr_t)&ungetc },
	{ "ungetwc", (uintptr_t)&ungetwc },
	{ "usleep", (uintptr_t)&usleep },
	{ "vasprintf", (uintptr_t)&vasprintf },
	{ "vfprintf", (uintptr_t)&vfprintf },
	{ "vprintf", (uintptr_t)&vprintf },
	{ "vsnprintf", (uintptr_t)&vsnprintf },
	{ "vsscanf", (uintptr_t)&vsscanf },
	{ "vsprintf", (uintptr_t)&vsprintf },
	{ "vswprintf", (uintptr_t)&vswprintf },
	{ "wcrtomb", (uintptr_t)&wcrtomb },
	{ "wcscoll", (uintptr_t)&wcscoll },
	{ "wcscmp", (uintptr_t)&wcscmp },
	{ "wcsncpy", (uintptr_t)&wcsncpy },
	{ "wcsftime", (uintptr_t)&wcsftime },
	{ "wcslen", (uintptr_t)&wcslen },
	{ "wcsxfrm", (uintptr_t)&wcsxfrm },
	{ "wctob", (uintptr_t)&wctob },
	{ "wctype", (uintptr_t)&wctype },
	{ "wmemchr", (uintptr_t)&wmemchr },
	{ "wmemcmp", (uintptr_t)&wmemcmp },
	{ "wmemcpy", (uintptr_t)&wmemcpy },
	{ "wmemmove", (uintptr_t)&wmemmove },
	{ "wmemset", (uintptr_t)&wmemset },
	{ "write", (uintptr_t)&write },
	{ "sigaction", (uintptr_t)&ret0 },
	{ "zlibVersion", (uintptr_t)&zlibVersion },
	// { "writev", (uintptr_t)&writev },
	{ "unlink", (uintptr_t)&unlink_hook },
	{ "Android_JNI_GetEnv", (uintptr_t)&Android_JNI_GetEnv },
	{ "nanosleep", (uintptr_t)&nanosleep_hook }, // FIXME
	{ "raise", (uintptr_t)&raise },
	{ "posix_memalign", (uintptr_t)&posix_memalign },
	{ "swprintf", (uintptr_t)&swprintf },
	{ "wcscpy", (uintptr_t)&wcscpy },
	{ "wcscat", (uintptr_t)&wcscat },
	{ "wcstombs", (uintptr_t)&wcstombs },
	{ "wcsstr", (uintptr_t)&wcsstr },
	{ "compress", (uintptr_t)&compress },
	{ "uncompress", (uintptr_t)&uncompress },
	{ "atof", (uintptr_t)&atof },
	{ "trunc", (uintptr_t)&trunc },
	{ "round", (uintptr_t)&round },
	{ "llrintf", (uintptr_t)&llrintf },
	{ "llrint", (uintptr_t)&llrint },
	{ "remove", (uintptr_t)&remove_hook },
	{ "__system_property_get", (uintptr_t)&ret0 },
	{ "strnlen", (uintptr_t)&strnlen },
};

int check_kubridge(void) {
	int search_unk[2];
	return _vshKernelSearchModuleByName("kubridge", search_unk);
}

enum MethodIDs {
	UNKNOWN = 0,
	INIT,
} MethodIDs;

typedef struct {
	char *name;
	enum MethodIDs id;
} NameToMethodID;

static NameToMethodID name_to_method_ids[] = {
	{ "<init>", INIT },
};

int GetMethodID(void *env, void *class, const char *name, const char *sig) {
	dlog("GetMethodID: %s\n", name);
	for (int i = 0; i < sizeof(name_to_method_ids) / sizeof(NameToMethodID); i++) {
		if (strcmp(name, name_to_method_ids[i].name) == 0) {
			return name_to_method_ids[i].id;
		}
	}

	return UNKNOWN;
}

int GetStaticMethodID(void *env, void *class, const char *name, const char *sig) {
	dlog("GetStaticMethodID: %s\n", name);
	for (int i = 0; i < sizeof(name_to_method_ids) / sizeof(NameToMethodID); i++) {
		if (strcmp(name, name_to_method_ids[i].name) == 0)
			return name_to_method_ids[i].id;
	}

	return UNKNOWN;
}

void CallStaticVoidMethodV(void *env, void *obj, int methodID, uintptr_t *args) {
}

int CallStaticBooleanMethodV(void *env, void *obj, int methodID, uintptr_t *args) {
	switch (methodID) {
	default:
		return 0;
	}
}

int CallStaticIntMethodV(void *env, void *obj, int methodID, uintptr_t *args) {
	switch (methodID) {
	default:
		return 0;	
	}
}

int64_t CallStaticLongMethodV(void *env, void *obj, int methodID, uintptr_t *args) {
	switch (methodID) {
	default:
		return 0;	
	}
}

uint64_t CallLongMethodV(void *env, void *obj, int methodID, uintptr_t *args) {
	return -1;
}

void *FindClass(void) {
	return (void *)0x41414141;
}

void *NewGlobalRef(void *env, char *str) {
	return (void *)0x42424242;
}

void DeleteGlobalRef(void *env, char *str) {
}

void *NewObjectV(void *env, void *clazz, int methodID, uintptr_t args) {
	return (void *)0x43434343;
}

void *GetObjectClass(void *env, void *obj) {
	return (void *)0x44444444;
}

char *NewStringUTF(void *env, char *bytes) {
	return bytes;
}

char *GetStringUTFChars(void *env, char *string, int *isCopy) {
	return string;
}

size_t GetStringUTFLength(void *env, char *string) {
	return strlen(string);	
}

int GetJavaVM(void *env, void **vm) {
	*vm = fake_vm;
	return 0;
}

int GetFieldID(void *env, void *clazz, const char *name, const char *sig) {
	return 0;
}

int GetBooleanField(void *env, void *obj, int fieldID) {
	return 1;
}

void *GetObjectArrayElement(void *env, uint8_t *obj, int idx) {
	return NULL;
}

int CallBooleanMethodV(void *env, void *obj, int methodID, uintptr_t *args) {
	switch (methodID) {
	default:
		return 0;
	}
}

char duration[32];
void *CallObjectMethodV(void *env, void *obj, int methodID, uintptr_t *args) {
	int lang = -1;
	switch (methodID) {
	default:
		return 0x34343434;
	}
}

int CallIntMethodV(void *env, void *obj, int methodID, uintptr_t *args) {
	switch (methodID) {
	default:
		return 0;
	}
}

void CallVoidMethodV(void *env, void *obj, int methodID, uintptr_t *args) {
	switch (methodID) {
	default:
		break;
	}
}

int GetStaticFieldID(void *env, void *clazz, const char *name, const char *sig) {
	return 0;
}

void *GetStaticObjectField(void *env, void *clazz, int fieldID) {
	switch (fieldID) {
	default:
		return NULL;
	}
}

void GetStringUTFRegion(void *env, char *str, size_t start, size_t len, char *buf) {
	sceClibMemcpy(buf, &str[start], len);
	buf[len] = 0;
}

void *CallStaticObjectMethodV(void *env, void *obj, int methodID, uintptr_t *args) {
	FILE *f;
	char *read_buf = NULL;
	size_t sz;
	switch (methodID) {
	default:
		return NULL;
	}
}

int GetIntField(void *env, void *obj, int fieldID) { return 0; }

float GetFloatField(void *env, void *obj, int fieldID) {
	switch (fieldID) {
	default:
		return 0.0f;
	}
}

float CallStaticFloatMethodV(void *env, void *obj, int methodID, uintptr_t *args) {
	switch (methodID) {
	default:
		if (methodID != UNKNOWN) {
			dlog("CallStaticDoubleMethodV(%d)\n", methodID);
		}
		return 0;
	}
}

int GetArrayLength(void *env, void *array) {
	dlog("GetArrayLength returned %d\n", *(int *)array);
	return *(int *)array;
}

/*int crasher(unsigned int argc, void *argv) {
	uint32_t *nullptr = NULL;
	for (;;) {
		SceCtrlData pad;
		sceCtrlPeekBufferPositive(0, &pad, 1);
		if (pad.buttons & SCE_CTRL_SELECT) *nullptr = 0;
		sceKernelDelayThread(100);
	}
}*/

#include <SDL2/SDL.h>
#include <SDL2/SDL_mixer.h>

Mix_Music *mus = NULL;
char real_fname[256];

int musicPlayerStart(void *this, char *fname, int unk, float vol) {
	sprintf(real_fname, "ux0:data/bullets/%s", fname);
	real_fname[strlen(real_fname) - 3] = 0;
	strcat(real_fname, "ogg");
	Mix_VolumeMusic((int)(vol * 128.0f));
	mus = Mix_LoadMUS(real_fname);
	Mix_PlayMusic(mus, -1);
	return 0;
}

int musicPlayerStop(void *this, int unk, int unk2, int unk3, int unk4, int unk5) {
	if (mus) {
		Mix_FreeMusic(mus);
		mus = NULL;
	}
	return 0;
}

int musicPlayerSetVolume(void *this, float vol) {
	Mix_VolumeMusic((int)(vol * 128.0f));
	return 0;
}

float musicPlayerGetVolume(void *this, float vol) {
	return (float)Mix_VolumeMusic(-1) / 128.0f;
}

void patch_game(void) {
	// Reimplementing Java music player with SDL2 Mixer
	if (SDL_Init(SDL_INIT_AUDIO) < 0) {
		fatal_error("Failed to init SDL2\n");
	}
	if (Mix_OpenAudio(48000, MIX_DEFAULT_FORMAT, 2, 4096)) {
		fatal_error("Failed to init SDL2 Mixer\n");
	}
	hook_addr(so_symbol(&main_mod, "_ZN16CJavaMusicPlayer5StartEPKcif"), (uintptr_t)musicPlayerStart);
	hook_addr(so_symbol(&main_mod, "_ZN16CJavaMusicPlayer4StopEv"), (uintptr_t)musicPlayerStop);
	hook_addr(so_symbol(&main_mod, "_ZN16CJavaMusicPlayer9SetVolumeEf"), (uintptr_t)musicPlayerSetVolume);
	hook_addr(so_symbol(&main_mod, "_ZN16CJavaMusicPlayer9GetVolumeEv"), (uintptr_t)musicPlayerGetVolume);
	
	hook_addr(so_symbol(&main_mod, "_ZN16FileUtilsAndroid4openEPKcS1_") + 4, (uintptr_t)fopen_hook);
	
	hook_addr(so_symbol(&main_mod, "alAuxiliaryEffectSlotf"), (uintptr_t)alAuxiliaryEffectSlotf);
	hook_addr(so_symbol(&main_mod, "alAuxiliaryEffectSlotfv"), (uintptr_t)alAuxiliaryEffectSlotfv);
	hook_addr(so_symbol(&main_mod, "alAuxiliaryEffectSloti"), (uintptr_t)alAuxiliaryEffectSloti);
	hook_addr(so_symbol(&main_mod, "alAuxiliaryEffectSlotiv"), (uintptr_t)alAuxiliaryEffectSlotiv);
	hook_addr(so_symbol(&main_mod, "alBuffer3f"), (uintptr_t)alBuffer3f);
	hook_addr(so_symbol(&main_mod, "alBuffer3i"), (uintptr_t)alBuffer3i);
	hook_addr(so_symbol(&main_mod, "alBufferData"), (uintptr_t)alBufferData);
	hook_addr(so_symbol(&main_mod, "alBufferSamplesSOFT"), (uintptr_t)alBufferSamplesSOFT);
	hook_addr(so_symbol(&main_mod, "alBufferSubDataSOFT"), (uintptr_t)alBufferSubDataSOFT);
	hook_addr(so_symbol(&main_mod, "alBufferSubSamplesSOFT"), (uintptr_t)alBufferSubSamplesSOFT);
	hook_addr(so_symbol(&main_mod, "alBufferf"), (uintptr_t)alBufferf);
	hook_addr(so_symbol(&main_mod, "alBufferfv"), (uintptr_t)alBufferfv);
	hook_addr(so_symbol(&main_mod, "alBufferi"), (uintptr_t)alBufferi);
	hook_addr(so_symbol(&main_mod, "alBufferiv"), (uintptr_t)alBufferiv);
	hook_addr(so_symbol(&main_mod, "alDeferUpdatesSOFT"), (uintptr_t)alDeferUpdatesSOFT);
	hook_addr(so_symbol(&main_mod, "alDeleteAuxiliaryEffectSlots"), (uintptr_t)alDeleteAuxiliaryEffectSlots);
	hook_addr(so_symbol(&main_mod, "alDeleteBuffers"), (uintptr_t)alDeleteBuffers);
	hook_addr(so_symbol(&main_mod, "alDeleteEffects"), (uintptr_t)alDeleteEffects);
	hook_addr(so_symbol(&main_mod, "alDeleteFilters"), (uintptr_t)alDeleteFilters);
	hook_addr(so_symbol(&main_mod, "alDeleteSources"), (uintptr_t)alDeleteSources);
	hook_addr(so_symbol(&main_mod, "alDisable"), (uintptr_t)alDisable);
	hook_addr(so_symbol(&main_mod, "alDistanceModel"), (uintptr_t)alDistanceModel);
	hook_addr(so_symbol(&main_mod, "alDopplerFactor"), (uintptr_t)alDopplerFactor);
	hook_addr(so_symbol(&main_mod, "alDopplerVelocity"), (uintptr_t)alDopplerVelocity);
	hook_addr(so_symbol(&main_mod, "alEffectf"), (uintptr_t)alEffectf);
	hook_addr(so_symbol(&main_mod, "alEffectfv"), (uintptr_t)alEffectfv);
	hook_addr(so_symbol(&main_mod, "alEffecti"), (uintptr_t)alEffecti);
	hook_addr(so_symbol(&main_mod, "alEffectiv"), (uintptr_t)alEffectiv);
	hook_addr(so_symbol(&main_mod, "alEnable"), (uintptr_t)alEnable);
	//hook_addr(so_symbol(&main_mod, "alEventCallbackSOFT"), (uintptr_t)alEventCallbackSOFT);
	//hook_addr(so_symbol(&main_mod, "alEventControlSOFT"), (uintptr_t)alEventControlSOFT);
	hook_addr(so_symbol(&main_mod, "alFilterf"), (uintptr_t)alFilterf);
	hook_addr(so_symbol(&main_mod, "alFilterfv"), (uintptr_t)alFilterfv);
	hook_addr(so_symbol(&main_mod, "alFilteri"), (uintptr_t)alFilteri);
	hook_addr(so_symbol(&main_mod, "alFilteriv"), (uintptr_t)alFilteriv);
	hook_addr(so_symbol(&main_mod, "alGenBuffers"), (uintptr_t)alGenBuffers);
	hook_addr(so_symbol(&main_mod, "alGenEffects"), (uintptr_t)alGenEffects);
	hook_addr(so_symbol(&main_mod, "alGenFilters"), (uintptr_t)alGenFilters);
	hook_addr(so_symbol(&main_mod, "alGenSources"), (uintptr_t)alGenSources);
	//hook_addr(so_symbol(&main_mod, "alFlushMappedBufferSOFT"), (uintptr_t)alFlushMappedBufferSOFT);
	hook_addr(so_symbol(&main_mod, "alGetAuxiliaryEffectSlotf"), (uintptr_t)alGetAuxiliaryEffectSlotf);
	hook_addr(so_symbol(&main_mod, "alGetAuxiliaryEffectSlotfv"), (uintptr_t)alGetAuxiliaryEffectSlotfv);
	hook_addr(so_symbol(&main_mod, "alGetAuxiliaryEffectSloti"), (uintptr_t)alGetAuxiliaryEffectSloti);
	hook_addr(so_symbol(&main_mod, "alGetAuxiliaryEffectSlotiv"), (uintptr_t)alGetAuxiliaryEffectSlotiv);
	hook_addr(so_symbol(&main_mod, "alGetBoolean"), (uintptr_t)alGetBoolean);
	hook_addr(so_symbol(&main_mod, "alGetBooleanv"), (uintptr_t)alGetBooleanv);
	hook_addr(so_symbol(&main_mod, "alGetBuffer3f"), (uintptr_t)alGetBuffer3f);
	hook_addr(so_symbol(&main_mod, "alGetBuffer3i"), (uintptr_t)alGetBuffer3i);
	hook_addr(so_symbol(&main_mod, "alGetBufferSamplesSOFT"), (uintptr_t)alGetBufferSamplesSOFT);
	hook_addr(so_symbol(&main_mod, "alGetBufferf"), (uintptr_t)alGetBufferf);
	hook_addr(so_symbol(&main_mod, "alGetBufferfv"), (uintptr_t)alGetBufferfv);
	hook_addr(so_symbol(&main_mod, "alGetBufferi"), (uintptr_t)alGetBufferi);
	hook_addr(so_symbol(&main_mod, "alGetBufferiv"), (uintptr_t)alGetBufferiv);
	hook_addr(so_symbol(&main_mod, "alGetDouble"), (uintptr_t)alGetDouble);
	hook_addr(so_symbol(&main_mod, "alGetDoublev"), (uintptr_t)alGetDoublev);
	hook_addr(so_symbol(&main_mod, "alGetEffectf"), (uintptr_t)alGetEffectf);
	hook_addr(so_symbol(&main_mod, "alGetEffectfv"), (uintptr_t)alGetEffectfv);
	hook_addr(so_symbol(&main_mod, "alGetEffecti"), (uintptr_t)alGetEffecti);
	hook_addr(so_symbol(&main_mod, "alGetEffectiv"), (uintptr_t)alGetEffectiv);
	hook_addr(so_symbol(&main_mod, "alGetEnumValue"), (uintptr_t)alGetEnumValue);
	hook_addr(so_symbol(&main_mod, "alGetError"), (uintptr_t)alGetError);
	hook_addr(so_symbol(&main_mod, "alGetFilterf"), (uintptr_t)alGetFilterf);
	hook_addr(so_symbol(&main_mod, "alGetFilterfv"), (uintptr_t)alGetFilterfv);
	hook_addr(so_symbol(&main_mod, "alGetFilteri"), (uintptr_t)alGetFilteri);
	hook_addr(so_symbol(&main_mod, "alGetFilteriv"), (uintptr_t)alGetFilteriv);
	hook_addr(so_symbol(&main_mod, "alGetFloat"), (uintptr_t)alGetFloat);
	hook_addr(so_symbol(&main_mod, "alGetFloatv"), (uintptr_t)alGetFloatv);
	hook_addr(so_symbol(&main_mod, "alGetInteger"), (uintptr_t)alGetInteger);
	hook_addr(so_symbol(&main_mod, "alGetIntegerv"), (uintptr_t)alGetIntegerv);
	//hook_addr(so_symbol(&main_mod, "alGetInteger64SOFT"), (uintptr_t)alGetInteger64SOFT);
	//hook_addr(so_symbol(&main_mod, "alGetInteger64vSOFT"), (uintptr_t)alGetInteger64vSOFT);
	hook_addr(so_symbol(&main_mod, "alGetListener3f"), (uintptr_t)alGetListener3f);
	hook_addr(so_symbol(&main_mod, "alGetListener3i"), (uintptr_t)alGetListener3i);
	hook_addr(so_symbol(&main_mod, "alGetListenerf"), (uintptr_t)alGetListenerf);
	hook_addr(so_symbol(&main_mod, "alGetListenerfv"), (uintptr_t)alGetListenerfv);
	hook_addr(so_symbol(&main_mod, "alGetListeneri"), (uintptr_t)alGetListeneri);
	hook_addr(so_symbol(&main_mod, "alGetListeneriv"), (uintptr_t)alGetListeneriv);
	//hook_addr(so_symbol(&main_mod, "alGetPointerSOFT"), (uintptr_t)alGetPointerSOFT);
	//hook_addr(so_symbol(&main_mod, "alGetPointervSOFT"), (uintptr_t)alGetPointervSOFT);
	hook_addr(so_symbol(&main_mod, "alGetProcAddress"), (uintptr_t)alGetProcAddress);
	hook_addr(so_symbol(&main_mod, "alGetSource3dSOFT"), (uintptr_t)alGetSource3dSOFT);
	hook_addr(so_symbol(&main_mod, "alGetSource3f"), (uintptr_t)alGetSource3f);
	hook_addr(so_symbol(&main_mod, "alGetSource3i"), (uintptr_t)alGetSource3i);
	hook_addr(so_symbol(&main_mod, "alGetSource3i64SOFT"), (uintptr_t)alGetSource3i64SOFT);
	hook_addr(so_symbol(&main_mod, "alGetSourcedSOFT"), (uintptr_t)alGetSourcedSOFT);
	hook_addr(so_symbol(&main_mod, "alGetSourcedvSOFT"), (uintptr_t)alGetSourcedvSOFT);
	hook_addr(so_symbol(&main_mod, "alGetSourcef"), (uintptr_t)alGetSourcef);
	hook_addr(so_symbol(&main_mod, "alGetSourcefv"), (uintptr_t)alGetSourcefv);
	hook_addr(so_symbol(&main_mod, "alGetSourcei"), (uintptr_t)alGetSourcei);
	hook_addr(so_symbol(&main_mod, "alGetSourcei64SOFT"), (uintptr_t)alGetSourcei64SOFT);
	hook_addr(so_symbol(&main_mod, "alGetSourcei64vSOFT"), (uintptr_t)alGetSourcei64vSOFT);
	hook_addr(so_symbol(&main_mod, "alGetSourceiv"), (uintptr_t)alGetSourceiv);
	hook_addr(so_symbol(&main_mod, "alGetString"), (uintptr_t)alGetString);
	hook_addr(so_symbol(&main_mod, "alGetStringiSOFT"), (uintptr_t)alGetStringiSOFT);
	hook_addr(so_symbol(&main_mod, "alIsAuxiliaryEffectSlot"), (uintptr_t)alIsAuxiliaryEffectSlot);
	hook_addr(so_symbol(&main_mod, "alIsBuffer"), (uintptr_t)alIsBuffer);
	hook_addr(so_symbol(&main_mod, "alIsBufferFormatSupportedSOFT"), (uintptr_t)alIsBufferFormatSupportedSOFT);
	hook_addr(so_symbol(&main_mod, "alIsEffect"), (uintptr_t)alIsEffect);
	hook_addr(so_symbol(&main_mod, "alIsEnabled"), (uintptr_t)alIsEnabled);
	hook_addr(so_symbol(&main_mod, "alIsExtensionPresent"), (uintptr_t)alIsExtensionPresent);
	hook_addr(so_symbol(&main_mod, "alIsFilter"), (uintptr_t)alIsFilter);
	hook_addr(so_symbol(&main_mod, "alIsSource"), (uintptr_t)alIsSource);
	hook_addr(so_symbol(&main_mod, "alListener3f"), (uintptr_t)alListener3f);
	hook_addr(so_symbol(&main_mod, "alListener3i"), (uintptr_t)alListener3i);
	hook_addr(so_symbol(&main_mod, "alListenerf"), (uintptr_t)alListenerf);
	hook_addr(so_symbol(&main_mod, "alListenerfv"), (uintptr_t)alListenerfv);
	hook_addr(so_symbol(&main_mod, "alListeneri"), (uintptr_t)alListeneri);
	hook_addr(so_symbol(&main_mod, "alListeneriv"), (uintptr_t)alListeneriv);
	//hook_addr(so_symbol(&main_mod, "alMapBufferSOFT"), (uintptr_t)alMapBufferSOFT);
	hook_addr(so_symbol(&main_mod, "alProcessUpdatesSOFT"), (uintptr_t)alProcessUpdatesSOFT);
	hook_addr(so_symbol(&main_mod, "alSetConfigMOB"), (uintptr_t)ret0);
	hook_addr(so_symbol(&main_mod, "alSource3dSOFT"), (uintptr_t)alSource3dSOFT);
	hook_addr(so_symbol(&main_mod, "alSource3f"), (uintptr_t)alSource3f);
	hook_addr(so_symbol(&main_mod, "alSource3i"), (uintptr_t)alSource3i);
	hook_addr(so_symbol(&main_mod, "alSource3i64SOFT"), (uintptr_t)alSource3i64SOFT);
	hook_addr(so_symbol(&main_mod, "alSourcePause"), (uintptr_t)alSourcePause);
	hook_addr(so_symbol(&main_mod, "alSourcePausev"), (uintptr_t)alSourcePausev);
	hook_addr(so_symbol(&main_mod, "alSourcePlay"), (uintptr_t)alSourcePlay);
	hook_addr(so_symbol(&main_mod, "alSourcePlayv"), (uintptr_t)alSourcePlayv);
	//hook_addr(so_symbol(&main_mod, "alSourceQueueBufferLayersSOFT"), (uintptr_t)alSourceQueueBufferLayersSOFT);
	hook_addr(so_symbol(&main_mod, "alSourceQueueBuffers"), (uintptr_t)alSourceQueueBuffers);
	hook_addr(so_symbol(&main_mod, "alSourceRewind"), (uintptr_t)alSourceRewind);
	hook_addr(so_symbol(&main_mod, "alSourceRewindv"), (uintptr_t)alSourceRewindv);
	hook_addr(so_symbol(&main_mod, "alSourceStop"), (uintptr_t)alSourceStop);
	hook_addr(so_symbol(&main_mod, "alSourceStopv"), (uintptr_t)alSourceStopv);
	hook_addr(so_symbol(&main_mod, "alSourceUnqueueBuffers"), (uintptr_t)alSourceUnqueueBuffers);
	hook_addr(so_symbol(&main_mod, "alSourcedSOFT"), (uintptr_t)alSourcedSOFT);
	hook_addr(so_symbol(&main_mod, "alSourcedvSOFT"), (uintptr_t)alSourcedvSOFT);
	hook_addr(so_symbol(&main_mod, "alSourcef"), (uintptr_t)alSourcef);
	hook_addr(so_symbol(&main_mod, "alSourcefv"), (uintptr_t)alSourcefv);
	hook_addr(so_symbol(&main_mod, "alSourcei"), (uintptr_t)alSourcei);
	hook_addr(so_symbol(&main_mod, "alSourcei64SOFT"), (uintptr_t)alSourcei64SOFT);
	hook_addr(so_symbol(&main_mod, "alSourcei64vSOFT"), (uintptr_t)alSourcei64vSOFT);
	hook_addr(so_symbol(&main_mod, "alSourceiv"), (uintptr_t)alSourceiv);
	hook_addr(so_symbol(&main_mod, "alSpeedOfSound"), (uintptr_t)alSpeedOfSound);
	//hook_addr(so_symbol(&main_mod, "alUnmapBufferSOFT"), (uintptr_t)alUnmapBufferSOFT);
	hook_addr(so_symbol(&main_mod, "alcCaptureCloseDevice"), (uintptr_t)alcCaptureCloseDevice);
	hook_addr(so_symbol(&main_mod, "alcCaptureOpenDevice"), (uintptr_t)alcCaptureOpenDevice);
	hook_addr(so_symbol(&main_mod, "alcCaptureSamples"), (uintptr_t)alcCaptureSamples);
	hook_addr(so_symbol(&main_mod, "alcCaptureStart"), (uintptr_t)alcCaptureStart);
	hook_addr(so_symbol(&main_mod, "alcCaptureStop"), (uintptr_t)alcCaptureStop);
	hook_addr(so_symbol(&main_mod, "alcCloseDevice"), (uintptr_t)alcCloseDevice);
	hook_addr(so_symbol(&main_mod, "alcCreateContext"), (uintptr_t)alcCreateContext);
	hook_addr(so_symbol(&main_mod, "alcDestroyContext"), (uintptr_t)alcDestroyContext);
	hook_addr(so_symbol(&main_mod, "alcDeviceEnableHrtfMOB"), (uintptr_t)ret0);
	hook_addr(so_symbol(&main_mod, "alcGetContextsDevice"), (uintptr_t)alcGetContextsDevice);
	hook_addr(so_symbol(&main_mod, "alcGetCurrentContext"), (uintptr_t)alcGetCurrentContext);
	hook_addr(so_symbol(&main_mod, "alcGetEnumValue"), (uintptr_t)alcGetEnumValue);
	hook_addr(so_symbol(&main_mod, "alcGetError"), (uintptr_t)alcGetError);
	hook_addr(so_symbol(&main_mod, "alcGetIntegerv"), (uintptr_t)alcGetIntegerv);
	hook_addr(so_symbol(&main_mod, "alcGetProcAddress"), (uintptr_t)alcGetProcAddress);
	hook_addr(so_symbol(&main_mod, "alcGetString"), (uintptr_t)alcGetString);
	hook_addr(so_symbol(&main_mod, "alcGetThreadContext"), (uintptr_t)alcGetThreadContext);
	hook_addr(so_symbol(&main_mod, "alcIsExtensionPresent"), (uintptr_t)alcIsExtensionPresent);
	hook_addr(so_symbol(&main_mod, "alcIsRenderFormatSupportedSOFT"), (uintptr_t)alcIsRenderFormatSupportedSOFT);
	hook_addr(so_symbol(&main_mod, "alcLoopbackOpenDeviceSOFT"), (uintptr_t)alcLoopbackOpenDeviceSOFT);
	hook_addr(so_symbol(&main_mod, "alcMakeContextCurrent"), (uintptr_t)alcMakeContextCurrent);
	hook_addr(so_symbol(&main_mod, "alcOpenDevice"), (uintptr_t)alcOpenDevice);
	hook_addr(so_symbol(&main_mod, "alcProcessContext"), (uintptr_t)alcProcessContext);
	hook_addr(so_symbol(&main_mod, "alcRenderSamplesSOFT"), (uintptr_t)alcRenderSamplesSOFT);
	hook_addr(so_symbol(&main_mod, "alcSetThreadContext"), (uintptr_t)alcSetThreadContext);
	hook_addr(so_symbol(&main_mod, "alcSuspendContext"), (uintptr_t)alcSuspendContext);
	
	hook_addr(so_symbol(&main_mod, "_ZN14NetworkManager4initEv"), (uintptr_t)ret0);
	hook_addr(so_symbol(&main_mod, "_ZN11NetworkNode3runEj"), (uintptr_t)ret0);
}

enum {
	MT_ACTION_DOWN,
	MT_ACTION_UP,
	MT_ACTION_MOVE,
	MT_ACTION_CANCEL,
	MT_ACTION_SCROLL
};

void *pthread_main(void *arg) {
	int (* JNI_OnLoad) (void *vm) = (void *)so_symbol(&main_mod, "JNI_OnLoad");
	int (* nativeStart) () = (void *)so_symbol(&main_mod, "Java_com_istomgames_engine_EngineActivity_nativeStart");
	int (* nativeInit) (void *env, void *obj, char *pkg_path, char *app_path, char *apk_name, void *asset_mgr) = (void *)so_symbol(&main_mod, "Java_com_istomgames_engine_GameRenderer_nativeInit");
	int (* nativeRender) () = (void *)so_symbol(&main_mod, "Java_com_istomgames_engine_GameRenderer_nativeRender");
	int (* nativeResize) (void *env, void *obj, int w, int h) = (void *)so_symbol(&main_mod, "Java_com_istomgames_engine_GameRenderer_nativeResize");
	int (* nativeTouch) (void *env, void *obj, int id, int action, float x, float y, int zero) = (void *)so_symbol(&main_mod, "Java_com_istomgames_engine_GameSurfaceView_nativeTouch");

	sceClibPrintf("JNI_OnLoad\n");
	JNI_OnLoad(fake_vm);
	
	sceClibPrintf("nativeInit\n");
	nativeInit(fake_env, NULL, "ux0:data/bullets", "ux0:data/bullets", "ux0:data/bullets", (void *)1);
	
	sceClibPrintf("nativeResize\n");
	nativeResize(fake_env, NULL, SCREEN_H, SCREEN_W);	
	
	sceClibPrintf("nativeStart\n");
	nativeStart();
	
	sceClibPrintf("Entering main loop\n");
	
	int lastX[SCE_TOUCH_MAX_REPORT] = {-1, -1, -1, -1, -1, -1, -1, -1};
	int lastY[SCE_TOUCH_MAX_REPORT] = {-1, -1, -1, -1, -1, -1, -1, -1};
	for (;;) {
		SceTouchData touch;
		sceTouchPeek(SCE_TOUCH_PORT_FRONT, &touch, 1);
				
		for (int i = 0; i < SCE_TOUCH_MAX_REPORT; i++) {
			if (i < touch.reportNum) {
				int x = (int)(touch.report[i].x * 0.5f);
				int y = (int)(touch.report[i].y * 0.5f);
				if (lastX[i] == -1 || lastY[i] == -1) {
					nativeTouch(fake_env, NULL, i, MT_ACTION_DOWN, x, y, 0);
				} else if (lastX[i] != x || lastY[i] != y) {
					nativeTouch(fake_env, NULL, i, MT_ACTION_MOVE, x, y, 0);
				}
				lastX[i] = x;
				lastY[i] = y;
			} else if (lastX[i] != -1 || lastY[i] != -1) {
				nativeTouch(fake_env, NULL, i, MT_ACTION_UP, lastX[i], lastY[i], 0);
				lastX[i] = -1;
				lastY[i] = -1;
			}
		}
		
		nativeRender();
		vglSwapBuffers(GL_FALSE);
	}
	
	return NULL;
}

int main(int argc, char *argv[]) {
	SceAppUtilInitParam init_param;
	SceAppUtilBootParam boot_param;
	memset(&init_param, 0, sizeof(SceAppUtilInitParam));
	memset(&boot_param, 0, sizeof(SceAppUtilBootParam));
	sceAppUtilInit(&init_param, &boot_param);
	
	//sceSysmoduleLoadModule(SCE_SYSMODULE_RAZOR_CAPTURE);
	//SceUID crasher_thread = sceKernelCreateThread("crasher", crasher, 0x40, 0x1000, 0, 0, NULL);
	//sceKernelStartThread(crasher_thread, 0, NULL);	
	
	sceTouchSetSamplingState(SCE_TOUCH_PORT_FRONT, SCE_TOUCH_SAMPLING_STATE_START);

	scePowerSetArmClockFrequency(444);
	scePowerSetBusClockFrequency(222);
	scePowerSetGpuClockFrequency(222);
	scePowerSetGpuXbarClockFrequency(166);

	if (check_kubridge() < 0)
		fatal_error("Error kubridge.skprx is not installed.");

	if (!file_exists("ur0:/data/libshacccg.suprx") && !file_exists("ur0:/data/external/libshacccg.suprx"))
		fatal_error("Error libshacccg.suprx is not installed.");
	
	char fname[256];
	sprintf(data_path, "ux0:data/bullets");
	
	sceClibPrintf("Loading libengine\n");
	sprintf(fname, "%s/libengine.so", data_path);
	if (so_file_load(&main_mod, fname, LOAD_ADDRESS) < 0)
		fatal_error("Error could not load %s.", fname);
	so_relocate(&main_mod);
	so_resolve(&main_mod, default_dynlib, sizeof(default_dynlib), 0);

	vglUseLowPrecision(GL_TRUE);
	vglSetSemanticBindingMode(VGL_MODE_POSTPONED);
	vglSetupRuntimeShaderCompiler(SHARK_OPT_UNSAFE, SHARK_ENABLE, SHARK_ENABLE, SHARK_ENABLE);
	vglInitExtended(0, SCREEN_W, SCREEN_H, 8 * 1024 * 1024, SCE_GXM_MULTISAMPLE_2X);

	patch_game();
	so_flush_caches(&main_mod);
	so_initialize(&main_mod);
	
	memset(fake_vm, 'A', sizeof(fake_vm));
	*(uintptr_t *)(fake_vm + 0x00) = (uintptr_t)fake_vm; // just point to itself...
	*(uintptr_t *)(fake_vm + 0x10) = (uintptr_t)ret0;
	*(uintptr_t *)(fake_vm + 0x14) = (uintptr_t)ret0;
	*(uintptr_t *)(fake_vm + 0x18) = (uintptr_t)GetEnv;

	memset(fake_env, 'A', sizeof(fake_env));
	*(uintptr_t *)(fake_env + 0x00) = (uintptr_t)fake_env; // just point to itself...
	*(uintptr_t *)(fake_env + 0x18) = (uintptr_t)FindClass;
	*(uintptr_t *)(fake_env + 0x4C) = (uintptr_t)ret0; // PushLocalFrame
	*(uintptr_t *)(fake_env + 0x50) = (uintptr_t)ret0; // PopLocalFrame
	*(uintptr_t *)(fake_env + 0x54) = (uintptr_t)NewGlobalRef;
	*(uintptr_t *)(fake_env + 0x58) = (uintptr_t)DeleteGlobalRef;
	*(uintptr_t *)(fake_env + 0x5C) = (uintptr_t)ret0; // DeleteLocalRef
	*(uintptr_t *)(fake_env + 0x74) = (uintptr_t)NewObjectV;
	*(uintptr_t *)(fake_env + 0x7C) = (uintptr_t)GetObjectClass;
	*(uintptr_t *)(fake_env + 0x84) = (uintptr_t)GetMethodID;
	*(uintptr_t *)(fake_env + 0x8C) = (uintptr_t)CallObjectMethodV;
	*(uintptr_t *)(fake_env + 0x98) = (uintptr_t)CallBooleanMethodV;
	*(uintptr_t *)(fake_env + 0xC8) = (uintptr_t)CallIntMethodV;
	*(uintptr_t *)(fake_env + 0xD4) = (uintptr_t)CallLongMethodV;
	*(uintptr_t *)(fake_env + 0xF8) = (uintptr_t)CallVoidMethodV;
	*(uintptr_t *)(fake_env + 0x178) = (uintptr_t)GetFieldID;
	*(uintptr_t *)(fake_env + 0x17C) = (uintptr_t)GetBooleanField;
	*(uintptr_t *)(fake_env + 0x190) = (uintptr_t)GetIntField;
	*(uintptr_t *)(fake_env + 0x198) = (uintptr_t)GetFloatField;
	*(uintptr_t *)(fake_env + 0x1C4) = (uintptr_t)GetStaticMethodID;
	*(uintptr_t *)(fake_env + 0x1CC) = (uintptr_t)CallStaticObjectMethodV;
	*(uintptr_t *)(fake_env + 0x1D8) = (uintptr_t)CallStaticBooleanMethodV;
	*(uintptr_t *)(fake_env + 0x208) = (uintptr_t)CallStaticIntMethodV;
	*(uintptr_t *)(fake_env + 0x21C) = (uintptr_t)CallStaticLongMethodV;
	*(uintptr_t *)(fake_env + 0x220) = (uintptr_t)CallStaticFloatMethodV;
	*(uintptr_t *)(fake_env + 0x238) = (uintptr_t)CallStaticVoidMethodV;
	*(uintptr_t *)(fake_env + 0x240) = (uintptr_t)GetStaticFieldID;
	*(uintptr_t *)(fake_env + 0x244) = (uintptr_t)GetStaticObjectField;
	*(uintptr_t *)(fake_env + 0x29C) = (uintptr_t)NewStringUTF;
	*(uintptr_t *)(fake_env + 0x2A0) = (uintptr_t)GetStringUTFLength;
	*(uintptr_t *)(fake_env + 0x2A4) = (uintptr_t)GetStringUTFChars;
	*(uintptr_t *)(fake_env + 0x2A8) = (uintptr_t)ret0; // ReleaseStringUTFChars
	*(uintptr_t *)(fake_env + 0x2AC) = (uintptr_t)GetArrayLength;
	*(uintptr_t *)(fake_env + 0x2B4) = (uintptr_t)GetObjectArrayElement;
	*(uintptr_t *)(fake_env + 0x35C) = (uintptr_t)ret0; // RegisterNatives
	*(uintptr_t *)(fake_env + 0x36C) = (uintptr_t)GetJavaVM;
	*(uintptr_t *)(fake_env + 0x374) = (uintptr_t)GetStringUTFRegion;

	pthread_t t2;
	pthread_attr_t attr2;
	pthread_attr_init(&attr2);
	pthread_attr_setstacksize(&attr2, 2 * 1024 * 1024);
	pthread_create(&t2, &attr2, pthread_main, NULL);

	return sceKernelExitDeleteThread(0);
}
