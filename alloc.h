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

#ifndef ALLOC_H
#define ALLOC_H

#include "value.h"

// Memory allocation

void memory_error(size_t size) __attribute__ ((noreturn, cold));

enum { alloc_modifyable = 0, alloc_normal = 1, alloc_atomic = 2 };

void* alloc(size_t size, int alloc_type) __attribute__ ((alloc_size(1), hot));
void* resize_alloc(void*, size_t size)   __attribute__ ((alloc_size(2), hot));

void* alloc_code();
void track_mmap_block(void*, size_t, size_t);

extern int pagesize;


// Root set stacks

extern struct hold_stack {
    Value *hot, *end, *cold;
} hold_stack;

void hold_stack_grow();

static inline void hold(Value x) {
    if (hold_stack.hot == hold_stack.end)
        hold_stack_grow();
    *hold_stack.hot++ = x;
}

static inline void release(size_t n) {
    hold_stack.hot -= n;
}


extern struct hold_mvalue_stack {
    MValue **hot, **end, **cold;
} hold_mvalue_stack;

void hold_mvalue_stack_grow();

static inline void hold_mvalue(MValue* x) {
    if (hold_mvalue_stack.hot == hold_mvalue_stack.end)
        hold_mvalue_stack_grow();
    *hold_mvalue_stack.hot++ = x;
}

static inline void release_mvalue(size_t n) {
    hold_mvalue_stack.hot -= n;
}


extern struct hold_array_stack {
    struct hold_array_stack_item {
        index n;
        const Value* p;
    } *hot, *end, *cold;
} hold_array_stack;

void hold_array_stack_grow();

static inline void hold_array(index n, const Value* p) {
    if (hold_array_stack.hot == hold_array_stack.end)
        hold_array_stack_grow();
    *hold_array_stack.hot++ = (struct hold_array_stack_item){ n, p };
}

static inline void release_array(size_t n) {
    hold_array_stack.hot -= n;
}


struct hold_save_buf {
    size_t hold, hold_mvalue, hold_array;
};

void hold_save(struct hold_save_buf*);
void hold_unroll(struct hold_save_buf*);


// Collector activation

#ifndef NDEBUG
void dump_heap();
#endif

void collect();

extern struct heap_size {
    size_t size, trigger;
} heap_size;

#define COLLECT() if (heap_size.size >= heap_size.trigger) collect()


#endif /* ALLOC_H */
