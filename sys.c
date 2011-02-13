/*
    Copyright 2010 Andrey Zholos

    This file is part of kuc, a vector programming language.

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include "sys.h"

#include "alloc.h"
#include "error.h"
#include "value.h"
#include "verb.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>


//
// File I/O
//

static ssize_t read_fd(int fd, void* buf, size_t size) {
    ssize_t i;
    while ((i = read(fd, buf, size)) == -1)
        if (errno != EINTR)
            return -1;
    return i;
}


static int close_fd(int fd) {
    while (close(fd) == -1)
        if (errno != EINTR)
            return -1;
    return 0;
}


static const char* filename(Value x) {
    if (x->vector || x->type != type_name || x->_name[0] != ':')
        error(error_type);
    return x->_name + 1;
}


#define MIN(x, y) ((x) < (y) ? (x) : (y))

Value read_file(Value x) {
    const char* fn = filename(x);
    int fd;
    while ((fd = open(fn, O_RDONLY)) == -1)
        if (errno != EINTR)
            goto error_file;

    // if we can find out the size, do so
    struct stat st;
    if (fstat(fd, &st) == -1)
        if (errno == EOVERFLOW)
            goto error_length_close;
        else
            goto error_file_close;

    if (st.st_size > index_max)
        goto error_length_close;

    MValue r = create_items(type_char, st.st_size);
    for (index n = 0;;) {
        if (n == r->count) {
            r->count = add_length(r->count, 1 << 16);
            r = resize_alloc(r, offsetof(struct value, items[0]) + r->count);
        }
        ssize_t i = read_fd(fd, r->chars + n, MIN(INT_MAX, r->count - n));
        if (i == -1)
            goto error_file_close;
        else if (i == 0) {
            r->count = n;
            r = resize_alloc(r, offsetof(struct value, items[0]) + r->count);
            break;
        } else
            n += i;
    }
    if (close_fd(fd) == -1)
        goto error_file;
    return r;

error_length_close:
    close_fd(fd);
    error(error_length);

error_file_close:
    close_fd(fd);
error_file:
    error(error_file);
}


Value write_file(Value x, Value y) {
    if (!y->vector || y->type != type_char)
        error(error_type);

    const char* fn = filename(x);
    int fd;
    while ((fd = open(fn, O_WRONLY | O_CREAT | O_TRUNC,
                          S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH)) == -1)
        if (errno != EINTR)
            goto error_file;

    for (index n = 0; n != y->count;) {
        ssize_t i = write(fd, y->chars + n, MIN(INT_MAX, y->count - n));
        if (i == -1 || i == 0) {
            if (i == -1 && errno == EINTR)
                continue;
            goto error_file_close;
        } else
            n += i;
    }
    if (close_fd(fd) == -1)
        goto error_file;
    return x;

error_file_close:
    close_fd(fd);
error_file:
    error(error_file);
}


Value mmap_file(Value x) {
    const char* fn = filename(x);
    int fd;
    while ((fd = open(fn, O_RDONLY)) == -1)
        if (errno != EINTR)
            goto error_file;

    struct stat st;
    if (fstat(fd, &st) == -1)
        if (errno == EOVERFLOW)
            goto error_length_close;
        else
            goto error_file_close;

    // we want to place one page (multiple pages if they're really small) in
    // front of the file in memory for the Value header
    size_t front = pagesize;
    front = (offsetof(struct value, items[0]) + (front - 1)) / front * front;
    if (st.st_size > SIZE_MAX - front || st.st_size > index_max)
        goto error_length_close;
    size_t total = front + st.st_size;

    // first, map and large enough segment of memory
    int flags = MAP_NOCORE;
    char* whole = mmap(0, total, PROT_NONE, flags | MAP_ANON, -1, 0);
    if (whole == MAP_FAILED)
        goto error_file_close;

    // then, map the file over it
    void* file = mmap(whole + front, total - front, PROT_READ,
                      flags | MAP_FIXED, fd, 0);
    if (file == MAP_FAILED)
        goto error_file_unmap;
    if (file != whole + front)
        assert_failed("mmap() didn't honor MAP_FIXED flag");

    // and put the header in front
    char* header = mmap(whole, front, PROT_READ | PROT_WRITE,
                        flags | MAP_FIXED | MAP_ANON, -1, 0);
    if (header == MAP_FAILED)
        goto error_file_unmap;
    if (header != whole)
        assert_failed("mmap() didn't honor MAP_FIXED flag");
    if (close_fd(fd) == -1)
        goto error_file_unmap;

    // since items is aligned and mapping is aligned, r should also be aligned
    size_t offset = front - offsetof(struct value, items[0]);
    MValue r = (MValue)(header + offset);
    r->type = type_char;
    r->vector = 1;
    r->count = st.st_size;

    track_mmap_block(r, total - offset, offset);
    return r;

error_length_close:
    close_fd(fd);
    error(error_length);

error_file_unmap:
    if (munmap(whole, total) == -1)
        assert_failed("munmap() failed");
error_file_close:
    close_fd(fd);
error_file:
    error(error_file);
}


//
// Random numbers
//

static void __attribute__ ((constructor)) init_random() {
  #if HAVE_SRANDOMDEV
    srandomdev();
  #else
    int fd = open("/dev/urandom", O_RDONLY);
    if (fd == -1)
        assert_failed("open(/dev/urandom) failed");
    unsigned long seed;
    if (read_fd(fd, &seed, sizeof seed) != sizeof seed)
        assert_failed("read(/dev/urandom) failed");
    if (close_fd(fd) == -1)
        assert_failed("close(/dev/urandom) failed");
    srandom(seed);
  #endif
}


static int draw_int(int bound) {
    assert(bound > 0);
    if (bound > RAND_MAX)
        assert_failed("random() doesn't have sufficient range");
    int draw = RAND_MAX / bound * bound;
    long r;
    do {
        r = random();
        if (r > RAND_MAX)
            assert_failed("random() > RAND_MAX");
    } while (r > draw);
    return r % bound;
}


Value draw(Value x) {
    if (x->vector) {
        return x->count > 0 ? item(x, INDEX_SUFFIX(draw)(x->count))
                            : item_null(x, 0);
    } else if (x->type == type_int) {
        if (x->_int <= 0)
            error(error_range);
        return create_int(draw_int(x->_int));
    } else
        error(error_todo);
}


//
// Timing
//

static Value time_delta(const struct timeval* t1, const struct timeval* t2) {
    if (t1->tv_sec >  t2->tv_sec ||
        t1->tv_sec == t2->tv_sec && t1->tv_usec > t2->tv_usec)
        error(error_sys);
    return create_float((t2->tv_sec         - t1->tv_sec) +
                        (t2->tv_usec * 1e-6 - t1->tv_usec * 1e-6));
}


Value time_value(Value x) {
    static const struct value_mixed key =
        { type_variant, 1, 3,
          { (Value)&name_user, (Value)&name_system, (Value)&name_value } };

    struct rusage rusage1, rusage2;
    if (getrusage(RUSAGE_SELF, &rusage1) == -1)
        error(error_sys);

    Value r = value(x);

    if (getrusage(RUSAGE_SELF, &rusage2) == -1)
        error(error_sys);

    return create_map((Value)&key, triplet(
        time_delta(&rusage1.ru_utime, &rusage2.ru_utime),
        time_delta(&rusage1.ru_stime, &rusage2.ru_stime), r));
}


//
// Terminal
//

index screen_size(index* height) {
    struct winsize ws;
    if (ioctl(STDIN_FILENO, TIOCGWINSZ, &ws) == -1) {
        // failures include there being no terminal
        ws.ws_col = 80;
        ws.ws_row = 25;
    }
    if (height)
        *height = ws.ws_row;
    return ws.ws_col;
}
