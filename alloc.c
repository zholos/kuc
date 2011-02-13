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

#include "alloc.h"

#include "adverb.h"
#include "code.h"
#include "func.h"
#include "value.h"

#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>

#define index index_hide /* index() should be in string.h anyway */
#include <string.h>
#undef index


//
// Memory allocation
//

void memory_error(size_t size) {
    fprintf(stderr, "error: couldn't allocate %zu bytes\n", size);
    exit(EXIT_FAILURE);
}


#if defined(NDEBUG) && !defined(NVALGRIND)
#define NVALGRIND
#endif

#ifndef NVALGRIND
#include <valgrind/memcheck.h>
#define REDZONE_ADJUST(x) ((x)+0)
#else
#define REDZONE_ADJUST(x) (x)
#endif


/* All block allocations are stored in a tree. Free nodes are also stored in one
   of several free lists. A block that has been collected is marked just-freed.
   After collection neighbouring free blocks are coalesced and just-freed blocks
   are placed on free lists.
*/

/* Non-atomic objects can become locked, after which they no longer need to be
   scanned at every collection, if:
   - they are not listed as held on the mvalue stack;
   - they are not the key or value of a map held on the mvalue stack;
   - they are not closures (modifyable);
   - they do not reference any persistent objects;
   - they do not reference any objects which are not locked (atomic objects are
     considered to be always locked).

   All objects referenced by a locked object are marked as persistent and do not
   get collected or scanned (scanning is unnecessary because they are either
   atomic or themselves locked). When a locked object is collected the objects
   it references revert from being persistent to being locked and thus become
   eligible for collection again.

   Thus, atomic objects can be in one of the following states (with
   corresponding marks):
        free                        (0)
        locked and marked white     (5 + white)
        locked and marked black     (5 + black)
        persistent and marked white (7 + white)
        persistent and marked black (7 + black)

    Non-atomic objects can be:
        free                        (0)
        unlockable and marked white (1 + white)
        unlockable and marked black (1 + black)
        unlocked and marked white   (3 + white)
        unlocked and marked black   (3 + black)
        locked and marked white     (5 + white)
        locked and marked black     (5 + black)
        persistent and marked white (7 + white)
        persistent and marked black (7 + black)

    Persistent objects still get marked if they are referenced by objects other
    than their locked referencer. If the referencer gets collected and the
    persistent object is marked white, it gets immediately collected as well.

    As new objects are made persistent, data which looks like pointers within
    locked objects can become pointers to them. All references to addresses
    within the bounds of allocation in a locked object must resolve to
    persistent objects so that there is no ambiguity when the object is
    unlocked. When the bounds of allocation change, all locks are removed.

    Large blocks which are used for small allocations have mark set 9.

    Nodes on a free list which are not zero-filled are marked atomic and are
    always marked non-special.
*/

// note: everything below invokes undefined behaviour by comparing pointers
// to different objects (6.5.8/5)


typedef uint16_t small_index;

typedef struct block {
    // tree structure in block tree
    struct block *block_left, *block_right;
    short block_balance;

    // allocation data
    char* base;
    size_t size;

    // flags
    char mark;
    bool atomic;
    char special; // 0 = none, 1 = code, 2 = mmap

    union {
        struct {
            // small block data
            unsigned short small_size;
            small_index small_count;
            small_index small_first_free; // SMALL_LAST means none are free
            small_index small_used;
            small_index* small_map;
#ifndef NVALGRIND
            unsigned short* small_alloced;
#endif
        };
        struct {
            // mmap block data
            size_t mmap_offset;
        };
        struct {
            // tree structure in free list
            struct block *free_left, *free_right;
            short free_balance;
        };
    };
}* Block;

#define TREE_PREFIX block
#define TREE_NODE Block
#define TREE_SAME( node, tree) ((node)->base == (tree)->base)
#define TREE_LEFT( node, tree) ((node)->base <  (tree)->base)
#define TREE_RIGHT(node, tree) ((node)->base >  (tree)->base)
#include "tree.h"

#define TREE_PREFIX free
#define TREE_NODE Block
#define TREE_SAME( node, tree) \
    ((node)->size == (tree)->size && (node)->base == (tree)->base)
#define TREE_LEFT( node, tree) ((node)->size < (tree)->size || \
     (node)->size == (tree)->size && (node)->base <  (tree)->base)
#define TREE_RIGHT(node, tree) ((node)->size > (tree)->size || \
     (node)->size == (tree)->size && (node)->base >  (tree)->base)
#include "tree.h"

Block block_tree, free_tree;
char *tree_min, *tree_max;
bool bounds_changed = 0;

typedef struct block_list {
    struct block_list* next;
    Block block;
}* BlockList;

char black = 0, white = 1;
struct heap_size heap_size;


static void* malloc_checked(size_t size) {
    void* memory = malloc(size);
    if (!memory)
        memory_error(size);
    return memory;
}


static void* realloc_checked(void* memory, size_t size) {
    void* new = realloc(memory, size);
    if (!new) {
        free(memory);
        memory_error(size);
    }
    return new;
}


static void list_push(BlockList* list, Block block) {
    BlockList front = malloc_checked(sizeof *front);
    front->next = *list;
    front->block = block;
    *list = front;
}


static Block list_pop(BlockList* list) {
    if (!*list)
        return NULL;
    Block block = (*list)->block;
    BlockList next = (*list)->next;
    free(*list);
    *list = next;
    return block;
}


/* Small allocations of uniform size are done from larger blocks. Each has an
   associated wordmap which also serves as a free list within that block (a free
   object word points to the next free object). Word value SMALL_LAST indicates
   that the item is the last in the free list. Word values above SMALL_LAST
   indicate that the item is not free and serve as collector marks.

   Small object sizes:
      Compound - references other objects:
               (smallest useful compound is 8 (sizeof(Value)))
         8; 16, 24, ..., 256  [17 sizes]
      Atomic: (note: smallest possible atomic is actually size 4 - char scalar)
         8; 16, 24, ..., 256  [17 types]
      Value-specific - prepared Value objects of certain type: (todo)
         ints, names          [2 types]
*/

// SMALL_MAX is the largest allocation using small blocks and the alignment of
// large allocations
#define SMALL_MAX 256
#define SMALL_STEP 16
#define SMALL_TYPES (SMALL_MAX / SMALL_STEP + 1)
#define SMALL_LAST (((index)UINT16_MAX + 1) / 2)

#define SMALL_OBJECT(block, memory) \
    (((memory) - (block)->base) / REDZONE_ADJUST((block)->small_size))
#define SMALL_ADDRESS(block, object) \
    ((block)->base + object * REDZONE_ADJUST((block)->small_size))

#ifndef NVALGRIND
#define SMALL_ALLOCED(block, object) (block)->small_alloced[object]
#else
#define SMALL_ALLOCED(block, object) (block)->small_size
#endif

BlockList small_list[2][SMALL_TYPES]; // [atomic][type]


// check that the maximum alignment requirement is not greater than 16
// fixme: if it's 32, small objects of size 24 are not useful because they're
// not properly aligned

struct check_align { char a; char b __attribute__ ((aligned)); };
typedef char check_align[-1+2*(int)(offsetof(struct check_align, b) <= 16)];


static void insert_block(Block block) {
    block->block_left    = NULL;
    block->block_right   = NULL;
    block->block_balance = 0;
    if (!block_tree) {
        block_tree = block;
        tree_min = block->base;
        tree_max = block->base + block->size;
        bounds_changed = 1;
    } else {
        block_insert_node(&block_tree, block);
        if (tree_min > block->base) {
            tree_min = block->base;
            bounds_changed = 1;
        } else if (tree_max < block->base + block->size) {
                   tree_max = block->base + block->size;
                   bounds_changed = 1;
        }
    }
}


static void remove_block(Block block) {
    block_remove_node(&block_tree, block);
    if (!block_tree)
        tree_max = tree_min = NULL;
    else if (tree_min == block->base) {
        Block min;
        for (min = block_tree; min->block_left; min = min->block_left);
        tree_min = min->base;
        bounds_changed = 1;
    } else if (tree_max == block->base + block->size) {
        Block max;
        for (max = block_tree; max->block_right; max = max->block_right);
        tree_max = max->base + max->size;
        bounds_changed = 1;
    }
}


static Block find_block(const char* base) {
    if (base >= tree_min && base < tree_max)
        for (Block block = block_tree; block;
                   block = base < block->base ? block->block_left
                                              : block->block_right)
            if (base >= block->base && base < block->base + block->size)
                return block;
    return NULL;
}


static void insert_free(Block block) {
    block->free_left    = NULL;
    block->free_right   = NULL;
    block->free_balance = 0;
    if (!free_tree)
        free_tree = block;
    else
        free_insert_node(&free_tree, block);
}


static void remove_free(Block block) {
    free_remove_node(&free_tree, block);
}


static Block alloc_block(size_t size, int alloc_type, bool small) {
    if (size > SIZE_MAX / 2)
        memory_error(size);

    Block fit = NULL;
    for (Block block = free_tree; block;
            block = size < block->size ? block->free_left : block->free_right)
        if (block->size == size) {
            fit = block;
            goto perfect_fit;
        } else if (block->size > size)
            fit = block;

    if (!fit) {
        size_t alloc = 1 << 24;
        for (; alloc < size; alloc *= 2);
        void* memory = mmap(0, alloc, PROT_READ | PROT_WRITE,
                            MAP_ANON | MAP_NOCORE, -1, 0);
        if (memory == MAP_FAILED)
            memory_error(alloc);

#ifndef NVALGRIND
        VALGRIND_MAKE_MEM_NOACCESS(memory, alloc);
#endif

        fit = malloc_checked(sizeof *fit);
        fit->base = memory;
        fit->size = alloc;
        fit->mark    = 0;
        fit->atomic  = 0;
        fit->special = 0;
        insert_block(fit);
        insert_free(fit);
    }

    if (fit->size >= size * 2) {
        // fixme: possibly align to smaller increments when Code objects are
        // allocated as full blocks (by jit)
        size_t lower = (size + (SMALL_MAX-1)) / SMALL_MAX * SMALL_MAX;
        if (fit->size > lower)  {
            Block upper = malloc_checked(sizeof *upper);
            upper->base    = fit->base + lower;
            upper->size    = fit->size - lower;
            upper->mark    = 0;
            upper->atomic  = fit->atomic;
            upper->special = 0;
            insert_block(upper);
            insert_free(upper);

            remove_free(fit);
            fit->size = lower;
            insert_free(fit);
        }
    }

perfect_fit:
    remove_free(fit);

    heap_size.size += fit->size;

    bool atomic = alloc_type / 2;
#ifndef NVALGRIND
    if (fit->atomic)
        VALGRIND_MAKE_MEM_UNDEFINED(fit->base, fit->size);
    else
        VALGRIND_MAKE_MEM_DEFINED(fit->base, fit->size);
#endif

    if (!atomic && fit->atomic)
        bzero(fit->base, fit->size); // note: sufficient to zero just size, but
                                     // the slack will create false references

    fit->mark   = small ? 9 : 1 + alloc_type*2 + black;
    fit->atomic = atomic;
    return fit;
}


static void prepare_small_block(BlockList* list,
                                unsigned short small_size, int alloc_type) {
    for (BlockList* item = list; *item; item = &(*item)->next) {
        assert((*item)->block->mark == 9);
        if ((*item)->block->small_first_free < SMALL_LAST) {
            if (item != list) {
                // move first free small block to the beginning of the list
                BlockList next = (*item)->next;
                (*item)->next = *list;
                *list = *item;
                *item = next;
            }
            return;
        }
    }

    // allocate a new small block; since the allocator can return blocks up to
    // twice the requested size, we request up to half the small_count we can
    // handle

    // note: the block must be of sufficient size not to be itself satisfiable
    // by a small allocation
    small_index small_count = small_size <= SMALL_STEP * 4  ? SMALL_LAST / 2 :
                              small_size <= SMALL_STEP * 8  ? SMALL_LAST / 4 :
                              small_size <= SMALL_STEP * 12 ? SMALL_LAST / 8 :
                                                              SMALL_LAST / 32;

    // fixme: temporarily reduce size of all small requests
    small_count /= 2;

    Block block = alloc_block(REDZONE_ADJUST(small_size) * small_count,
                              alloc_type, 1);
    small_count = block->size / REDZONE_ADJUST(small_size);
    assert(small_count <= SMALL_LAST);
    block->small_size  = small_size;
    block->small_count = small_count;
    block->small_first_free = 0;
    block->small_used = 0;
    block->small_map = malloc_checked(sizeof *block->small_map * small_count);
    for (index i = 0; i < small_count-1; i++)
        block->small_map[i] = i + 1;
    block->small_map[small_count-1] = SMALL_LAST;
#ifndef NVALGRIND
    block->small_alloced =
        malloc_checked(sizeof *block->small_alloced * small_count);
    VALGRIND_CREATE_MEMPOOL(block->base, REDZONE_ADJUST(0), !(alloc_type / 2));
#endif

    list_push(list, block);
}


static int small_type(size_t size) {
    return size <= 8 ? 0 : (size + SMALL_STEP-1) / SMALL_STEP;
}


void* alloc(size_t size, int alloc_type) {
    if (size <= SMALL_MAX) {
        int type = small_type(size);
        unsigned short small_size = type == 0 ? 8 : SMALL_STEP * type;

        bool atomic = alloc_type / 2;
        if (!small_list[atomic][type] ||
             small_list[atomic][type]->block->small_first_free == SMALL_LAST)
            prepare_small_block(&small_list[atomic][type],
                                 small_size, alloc_type);

        Block block = small_list[atomic][type]->block;
        assert(block->small_size == small_size &&
               block->small_first_free < SMALL_LAST);
        index object = block->small_first_free;
        assert(block->small_map[object] <= SMALL_LAST);
        block->small_first_free = block->small_map[object];
        block->small_used++;
        block->small_map[object] = SMALL_LAST + 1 + alloc_type*2 + black;
        char* memory = block->base + object * REDZONE_ADJUST(small_size);
#ifndef NVALGRIND
        block->small_alloced[object] = size;
        VALGRIND_MEMPOOL_ALLOC(block->base, memory, small_size);
#endif
        if (!atomic)
            bzero(memory, small_size);
        else if (size < small_size)
            bzero(memory + size, small_size - size);
#ifndef NVALGRIND
        if (size < small_size)
            VALGRIND_MAKE_MEM_NOACCESS(memory + size, small_size - size);
#endif
        return memory;
    } else
        return alloc_block(size, alloc_type, 0)->base;
}


static void free_block(Block block) {
    heap_size.size -= block->size;

    if (block->size >= (1 << 20))
        madvise(block->base, block->size - block->size % pagesize, MADV_FREE);

#ifndef NVALGRIND
    VALGRIND_MAKE_MEM_NOACCESS(block->base, block->size);
#endif

    block->mark   = 0;
    block->atomic = 1; // zero it on allocation
    insert_free(block);
}


void* resize_alloc(void* memory, size_t size) {
    Block block = find_block(memory);
    assert(block && block->mark);
    if (block->mark == 9) {
        // note: this check is important
        index object = SMALL_OBJECT(block, (char*)memory);
        assert(object < SMALL_LAST && block->small_map[object] > SMALL_LAST);
        assert(memory == SMALL_ADDRESS(block, object));

#ifndef NVALGRIND
        unsigned short alloced = block->small_alloced[object];
#else
        unsigned short alloced = block->small_size;
#endif

        // mostly objects will grow, not shrink, so don't look for a smaller
        // block
        if (size <= block->small_size) {
            if (!block->atomic && size < alloced)
                bzero((char*)memory + size, alloced - size);
#ifndef NVALGRIND
            block->small_alloced[object] = size;
            if (size >= alloced)
                VALGRIND_MAKE_MEM_UNDEFINED((char*)memory + alloced,
                                             size - alloced);
            else
                VALGRIND_MAKE_MEM_NOACCESS((char*)memory + size,
                                            alloced - size);
#endif
            return memory;
        }

        char* new = alloc(size, block->atomic ? alloc_atomic :
                                block->small_map[object] >= SMALL_LAST + 3);
        memcpy(new, memory, MIN(size, alloced));

        block->small_map[object] = block->small_first_free;
        block->small_first_free = object;
        block->small_used--;
#ifndef NVALGRIND
        VALGRIND_MEMPOOL_FREE(block->base, memory);
#endif
        return new;

    } else {
        assert(memory == block->base);

        // mostly objects will grow, not shrink
        if (size <= block->size) {
            if (!block->atomic)
                bzero(block->base + size, block->size - size);
            return memory;
        }

        char* new = alloc(size, block->atomic ? alloc_atomic :
                                block->mark >= 3);
        memcpy(new, memory, MIN(block->size, size));

        free_block(block);
        return new;
    }
}


void* alloc_code() {
#ifndef NJIT
    Block block = alloc_block(sizeof(struct code), alloc_normal, 0);
    block->special = 1;
    return block->base;
#else
    return alloc(sizeof(struct code), alloc_normal);
#endif
}


void track_mmap_block(void* base, size_t size, size_t mmap_offset) {
    Block block = malloc_checked(sizeof *block);
    block->base = base;
    block->size = size;
    block->mark    = 5 + black; // atomic
    block->atomic  = 1;
    block->special = 2;
    block->mmap_offset = mmap_offset;
    insert_block(block);
}


int pagesize;

void __attribute__ ((constructor)) pagesize_init() {
    pagesize = getpagesize();
    if (pagesize <= 0)
        assert_failed("getpagesize() returned impossible value");
}


//
// Root set stacks
//

#define HOLD_STACK(name)                                                  \
struct name name;                                                         \
                                                                          \
/* must grow by at least two elements */                                  \
void name##_grow() {                                                      \
    size_t count = name.hot - name.cold,                                  \
           size  = name.end - name.cold;                                  \
    size = MAX(1 << 16, size * 2);                                        \
    name.cold = realloc_checked(name.cold, size * sizeof *name.cold);     \
    name.hot = name.cold + count;                                         \
    name.end = name.cold + size;                                          \
}                                                                         \
                                                                          \
void name##_shrink() {                                                    \
    size_t count = name.hot - name.cold,                                  \
           size  = name.end - name.cold;                                  \
    if (       count <= size / 4 && size / 4 >= 1 << 16) {                \
        for (; count <= size / 2 && size / 2 >= 1 << 16; size /= 2);      \
        name.cold = realloc_checked(name.cold, size * sizeof *name.cold); \
        name.hot = name.cold + count;                                     \
        name.end = name.cold + size;                                      \
    }                                                                     \
}

HOLD_STACK(hold_stack)
HOLD_STACK(hold_mvalue_stack)
HOLD_STACK(hold_array_stack)


void hold_save(struct hold_save_buf* buf) {
    buf->hold        = hold_stack.hot        - hold_stack.cold;
    buf->hold_mvalue = hold_mvalue_stack.hot - hold_mvalue_stack.cold;
    buf->hold_array  = hold_array_stack.hot  - hold_array_stack.cold;
}


void hold_unroll(struct hold_save_buf* buf) {
    assert(hold_stack.hot        - hold_stack.cold        >= buf->hold);
    assert(hold_mvalue_stack.hot - hold_mvalue_stack.cold >= buf->hold_mvalue);
    assert(hold_array_stack.hot  - hold_array_stack.cold  >= buf->hold_array);

    hold_stack.hot        = hold_stack.cold        + buf->hold;
    hold_mvalue_stack.hot = hold_mvalue_stack.cold + buf->hold_mvalue;
    hold_array_stack.hot  = hold_array_stack.cold  + buf->hold_array;
}


//
// Heap management and collection
//

#ifndef NDEBUG

static int verify_tree(Block tree) {
    int left  = tree->block_left  ? verify_tree(tree->block_left)  : 0;
    int right = tree->block_right ? verify_tree(tree->block_right) : 0;
    assert(tree->block_balance >= -1 && tree->block_balance <= 1 &&
           tree->block_balance == left - right);
    return 1 + MAX(left, right);
}


static void verify_small_block(Block block) {
    assert(block->small_count <= SMALL_LAST);
    assert(REDZONE_ADJUST(block->small_size) ==
           block->size / block->small_count);

    index free_found = 0;
    for (small_index free = block->small_first_free;;
            free = block->small_map[free]) {
        if (free == SMALL_LAST)
            break;
        assert(free < block->small_count);
        free_found++;
        assert(free_found <= block->small_count); // detect cycles
    }
    assert(free_found + block->small_used == block->small_count);

    for (small_index i = 0; i < block->small_count; i++) {
        if (block->small_map[i] <= SMALL_LAST)
            free_found--;
        else
            assert((block->small_map[i] == SMALL_LAST + 1 + black ||
                    block->small_map[i] == SMALL_LAST + 3 + black) &&
                        !block->atomic ||
                    block->small_map[i] == SMALL_LAST + 5 + black ||
                    block->small_map[i] == SMALL_LAST + 7 ||
                    block->small_map[i] == SMALL_LAST + 8);
    }
    assert(!free_found);

}


static void verify_heap(Block block) {
    if (block->mark)
        if (block->mark == 9)
            verify_small_block(block);
        else
            assert((block->mark == 1 + black || block->mark == 3 + black)
                        && !block->atomic ||
                    block->mark == 5 + black ||
                    block->mark == 7 || block->mark == 8);
}


void dump_heap_tree(Block block) {
    if (block->block_left)
        dump_heap_tree(block->block_left);

    printf("[ %p, %9zu ]: %6s", block->base, block->size,
           !block->mark ? "free" : block->atomic ? "atomic" : "");
    if (block->mark)
        if (block->mark == 9)
            printf("   small: [ %3hu ], %4d free",
                   block->small_size, block->small_count - block->small_used);
        else if (block->special)
            printf("   %s", block->special == 1 ? "code" : "mmap");
    putchar('\n');

    if (block->block_right)
        dump_heap_tree(block->block_right);
}


void dump_heap() {
    if (block_tree)
        dump_heap_tree(block_tree);
    printf("total bytes: %zu, "
           "root values: %td, root mvalues: %td, root arrays: %td\n",
           heap_size.size,
           hold_stack.hot        - hold_stack.cold,
           hold_mvalue_stack.hot - hold_mvalue_stack.cold,
           hold_array_stack.hot  - hold_array_stack.cold);
}

#endif /* NDEBUG */


/* Objects allocated with alloc() and the pointers they contain:

    struct value:
      which contains pointers in item:
        map:    key and value
        func:   code and closure
        proj:   func and args
        comp:   [0] and [1]
        clause: verb
      and pointers in items:
        variant vector

    struct code:          instr and literals
    struct code.instr:    atomic
    struct code.literals: pointer array

    struct proj.args:     pointer array
    struct func.upvalues: pointer array (modifyable)

    All pointers should be aligned, and thus it is faster to scan entire
    non-atomic object representations for pointers, rather than determining
    their types and scanning object pointer members.

   (A matching object representation is not required for different pointer
    types, but we check their size equality at least.)
*/

#define CHECK_SIZE(type, name) typedef char \
    check_size_##name[(sizeof(void*)==sizeof(type name*))*2-1];

CHECK_SIZE(,       char)
CHECK_SIZE(struct, value)
CHECK_SIZE(struct, code)

#define CHECK_ALIGN(type, name, member) typedef char         \
    check_align_##name##_##member[1 - 2 *                    \
        (int)(offsetof(type name, member) % sizeof(void*))];

CHECK_ALIGN(struct, value,  map)
CHECK_ALIGN(,       Map,    key)
CHECK_ALIGN(,       Map,    value)
CHECK_ALIGN(struct, value,  func)
CHECK_ALIGN(,       Func,   code)
CHECK_ALIGN(,       Func,   upvalues)
CHECK_ALIGN(struct, value,  proj)
CHECK_ALIGN(,       Proj,   func)
CHECK_ALIGN(,       Proj,   args)
CHECK_ALIGN(struct, value,  clause)
CHECK_ALIGN(,       Clause, verb)
CHECK_ALIGN(struct, value,  items)
CHECK_ALIGN(struct, code,   instr)
CHECK_ALIGN(struct, code,   literals)


static bool is_mvalue(const void* base) {
    for (MValue** p = hold_mvalue_stack.cold; p != hold_mvalue_stack.hot; p++) {
        if (**p == base)
            return 1;

        // fixme: all mvalues must be initialized during collection
        if ((**p)->type == type_map && ((**p)->map.key == base ||
                                        (**p)->map.value == base))
            return 1;
    }
    return 0;
}


// returns true if one of the referenced objects prevented locking
static bool look_persist(const char* const* p_start, size_t size) {
    const char* const* p = p_start;
    const char* const* p_end = p + size / sizeof *p;
    for (; p < p_end; p++) {
        if (*p < tree_min || *p >= tree_max)
            continue;

        Block found = find_block(*p);
        if (found && found->mark)
            if (found->mark == 9) {
                index object = SMALL_OBJECT(found, *p);
                char* base = SMALL_ADDRESS(found, object);
                if (*p == base && found->small_map[object] > SMALL_LAST) {
                    if (found->small_map[object] == SMALL_LAST + 5 + black) {
                        found->small_map[object] =  SMALL_LAST + 7 + black;
                        // see below
                        goto next;
                    }
                    goto check_duplicate;
                }
            } else
                if (*p == found->base) {
                    if (found->mark == 5 + black) {
                        found->mark =  7 + black;
                        // assume other objects reference it, however, this is
                        // irrelevant because the locked object won't be
                        // collected this iteration
                        goto next;
                    }

                check_duplicate:
                    for (const char* const* q = p_start; q != p; q++)
                        if (*q == *p)
                            goto next;
                }

        // can't make persistent: change everything back and return
        p_end = p;
        for (p = p_start; p < p_end; p++) {
            if (*p < tree_min || *p >= tree_max)
                continue;

            Block found = find_block(*p);
            assert(found && found->mark);
            if (found->mark == 9) {
                index object = SMALL_OBJECT(found, *p);
                assert(*p == SMALL_ADDRESS(found, object));
                if (found->small_map[object] == SMALL_LAST + 7 + black)
                    found->small_map[object] =  SMALL_LAST + 5 + black;
#ifndef NDEBUG
                else
                    goto unpersist_check_duplicate;
#endif
            } else {
                assert(*p == found->base);
                if (found->mark == 7 + black)
                    found->mark =  5 + black;
#ifndef NDEBUG
                else {
                unpersist_check_duplicate:
                    for (const char* const* q = p_start; q != p; q++)
                        if (*q == *p)
                            goto unpersist_next;
                    assert(0);
                unpersist_next:;
                }
#endif
            }
        }
        return 1;

    next:;
    }
    return 0;
}


static bool mark(Block block, const char* p);

static inline bool look_see(const char* p) {
    Block found = find_block(p);
    if (found && found->mark)
        return mark(found, p);
    return 0;
}


// returns true if this object can't be locked
static bool look(const char* const* p, size_t size) {
#ifndef NVALGRIND
    // a zero-length array may be in the root set, which means the pointer p
    // doesn't matter, but Valgrind will complain about the p < p_end comparison
    if (!size)
        return 0;
#endif
    const char* const* p_end = p + size / sizeof *p;
    for (; p < p_end; p++)
        if (look_see(*p)) {
            for (p++; p < p_end; p++)
                look_see(*p);
            return 1;
        }
    return 0;
}


// returns true if this object prevents the referencer from being locked (i.e.,
// is persistent or unlocked non-atomic)
static bool mark(Block block, const char* p) {
    if (block->mark == 9) {
        index object = SMALL_OBJECT(block, p);
        assert(object >= 0 && object < block->small_count);

        // ignore internal pointers
        const char* base = SMALL_ADDRESS(block, object);
        if (p != base)
            return 0;

        small_index map = block->small_map[object];
        if (map <= SMALL_LAST) // free
            return 0;

        map -= SMALL_LAST;
        if (map == 7 + black || map == 3 + black || map == 1 + black)
            return 1;
        if (map == 5 + black)
            return 0;

        if (map == 3 + white) {
            block->small_map[object] = SMALL_LAST + 3 + black;
            unsigned short alloced = SMALL_ALLOCED(block, object);
            if (!look((const char* const*)base, alloced) &&
                    !is_mvalue(base) &&
                    !look_persist((const char* const*)base, alloced))
                // lock object
                goto small_locked;
            return 1;
        } else if (map == 5 + white) {
        small_locked:
            block->small_map[object] = SMALL_LAST + 5 + black;
            return 0;
        } else if (map == 1 + white) {
            block->small_map[object] = SMALL_LAST + 1 + black;
            unsigned short alloced = SMALL_ALLOCED(block, object);
            look((const char* const*)base, alloced);
            return 1;
        } else {
            assert(map == 7 + white);
            block->small_map[object] = SMALL_LAST + 7 + black;
            return 1;
        }

    } else if (block->mark) {
        // ignore internal pointers to large allocations
        if (p != block->base)
            return 0;

        // already marked or persistent
        if (block->mark == 7 + black || block->mark == 3 + black
                                     || block->mark == 1 + black)
            return 1;
        if (block->mark == 5 + black)
            return 0;

        if (block->mark == 3 + white) {
            block->mark  = 3 + black;
            if (!look((const char* const*)block->base, block->size) &&
                    !is_mvalue(block->base) &&
                    !look_persist((const char* const*)block->base, block->size))
                // lock object
                goto locked;
            return 1;
        } else if (block->mark == 5 + white) {
        locked:
            block->mark = 5 + black;
            return 0;
        } else if (block->mark == 1 + white) {
            block->mark = 1 + black;
            look((const char* const*)block->base, block->size);
            return 1;
        } else {
            assert(block->mark == 7 + white);
            block->mark = 7 + black;
            return 1;
        }
    } else
        return 0; // free block
}


struct sweep_state {
    Block last_free;
    bool hold_free;
    BlockList coalesced;
    BlockList munmap;
};


static void sweep_unpersist(struct sweep_state* state, const char* current,
                            const char* const* p_start, size_t size) {
    const char* const* p = p_start;
    const char* const* p_end = p + size / sizeof *p;
    for (; p < p_end; p++) {
        if (*p < tree_min || *p >= tree_max)
            continue;

        Block block = find_block(*p);
        assert(block && block->mark);

        if (block->mark == 9) {
            index object = SMALL_OBJECT(block, *p);
            char* base = SMALL_ADDRESS(block, object);
            assert(*p == base);
            if (block->small_map[object] == SMALL_LAST + 7 + black)
                block->small_map[object] =  SMALL_LAST + 5 + black;
            else if (block->small_map[object] == SMALL_LAST + 7 + white) {
                assert(base != current);
                if (base > current)
                    block->small_map[object] = SMALL_LAST + 5 + white;
                else {
                    if (!block->atomic)
                        sweep_unpersist(state, current, (const char* const*)
                                        base, SMALL_ALLOCED(block, object));
                    block->small_map[object] = block->small_first_free;
                    block->small_first_free = object;
                    block->small_used--;
#ifndef NVALGRIND
                    VALGRIND_MEMPOOL_FREE(block->base, base);
#endif
                }
            }
#ifndef NDEBUG
            else
                goto unpersist_check_duplicate;
#endif

        } else {
            assert(*p == block->base);
            if (block->mark == 7 + black)
                block->mark =  5 + black;
            else if (block->mark == 7 + white) {
                assert(block->base != current);
                if (block->base > current)
                    block->mark = 5 + white;
                    // the block will be collected in the continuing sweep
                else {
                    // follow sweep logic below
                    if (!block->atomic)
                        sweep_unpersist(state, current, (const char* const*)
                                        block->base, block->size);
                    if (block->special == 2)
                        list_push(&state->munmap, block);
                    else {
#ifndef NJIT
                        if (block->special == 1) {
                            block->special = 0;
                            code_finalize((Code)block->base);
                        }
#endif
                        free_block(block);
                    }
                }
            }
#ifndef NDEBUG
            else {
            unpersist_check_duplicate:
                for (const char* const* q = p_start; q != p; q++)
                    if (*q == *p)
                        goto unpersist_next;
                assert(0);
            unpersist_next:;
            }
#endif
        }
    }
}


static void sweep(struct sweep_state* state, Block block) {
    // traverse tree in left-to-right order
    if (block->block_left)
        sweep(state, block->block_left);

    if (block->mark == 9) {
        index last_free = block->small_first_free;
        small_index freed = 0;
        small_index locked     = SMALL_LAST + 5 + white,
                    unlocked   = SMALL_LAST + 3 + white,
                    unlockable = SMALL_LAST + 1 + white;

        for (index object = 0; object < block->small_count; object++) {
            if (block->small_map[object] == locked && !block->atomic) {
                const char* base = SMALL_ADDRESS(block, object);
                sweep_unpersist(state, base, (const char* const*)
                                base, SMALL_ALLOCED(block, object));
            }
            if (block->small_map[object] == locked ||
                block->small_map[object] == unlocked ||
                block->small_map[object] == unlockable) {
                block->small_map[object] = last_free;
                last_free = object;
                freed++;
#ifndef NVALGRIND
                VALGRIND_MEMPOOL_FREE(block->base,
                                      SMALL_ADDRESS(block, object));
#endif
            }
        }

        if (freed) {
            block->small_first_free = last_free;
            block->small_used -= freed;
            if (!block->small_used) {
                int type = small_type(block->small_size);
                for (BlockList* small = &small_list[block->atomic][type];;
                                small = &(*small)->next)
                    if ((*small)->block == block) {
                        list_pop(small);
                        goto found_small_item;
                    }
                assert(0);

            found_small_item:
                free(block->small_map);
#ifndef NVALGRIND
                free(block->small_alloced);
                VALGRIND_DESTROY_MEMPOOL(block->base);
                VALGRIND_MAKE_MEM_UNDEFINED(block->base, block->size);
#endif
                free_block(block);
                goto coalesce;
            }
        }

    } else if (block->mark) {
        if (block->mark == 5 + white && !block->atomic)
            sweep_unpersist(state, block->base,
                            (const char* const*)block->base, block->size);
        if (block->mark == 5 + white || block->mark == 3 + white
                                     || block->mark == 1 + white)
            if (block->special == 2)
                list_push(&state->munmap, block);
            else {
#ifndef NJIT
                if (block->special == 1) {
                    block->special = 0;
                    code_finalize((Code)block->base);
                }
#endif
                free_block(block);
                goto coalesce;
            }

    } else
    coalesce:
        if (state->last_free && state->last_free->base +
                                state->last_free->size == block->base) {
            if (!state->hold_free) {
                state->hold_free = 1;
                remove_free(state->last_free);
            }

            state->last_free->size += block->size;
            if (block->atomic)
                state->last_free->atomic = 1;
            remove_free(block);
            list_push(&state->coalesced, block);
        } else {
            if (state->hold_free) {
                insert_free(state->last_free);
                state->hold_free = 0;
            }
            state->last_free = block;
        }

    if (block->block_right)
        sweep(state, block->block_right);
}


static void unlock_all(Block block) {
    if (block->block_left)
        unlock_all(block->block_left);

    if (block->mark == 9) {
        for (index object = 0; object < block->small_count; object++) {
            small_index map = block->small_map[object];
            assert(map != SMALL_LAST + 3 + white &&
                   map != SMALL_LAST + 5 + white);
            if (map == SMALL_LAST + 7 || map == SMALL_LAST + 8 ||
                    !block->atomic && map == SMALL_LAST + 5 + black)
                block->small_map[object] =
                    SMALL_LAST + (block->atomic ? 5 : 3) + black;
        }
    } else if (block->mark) {
        assert(block->mark != 3 + white && block->mark != 5 + white);
        if (block->mark == 7 || block->mark == 8 ||
                !block->atomic && block->mark == 5 + black)
            block->mark = (block->atomic ? 5 : 3) + black;
    }

    if (block->block_right)
        unlock_all(block->block_right);
}


void collect() {
    if (bounds_changed) {
        unlock_all(block_tree);
        bounds_changed = 0;
    }

    white = black;
    black = 1 - black;

    //printf("collecting\n");
    for (Value* p = hold_stack.cold; p != hold_stack.hot; p++)
        look_see((char*)*p);

    for (MValue** p = hold_mvalue_stack.cold; p != hold_mvalue_stack.hot; p++)
        look_see((char*)**p);

    for (struct hold_array_stack_item* p =  hold_array_stack.cold;
                                       p != hold_array_stack.hot; p++)
        look((const char* const*)p->p, p->n * sizeof(char*));

    if (block_tree) {
        struct sweep_state state = { NULL, 0, NULL, NULL };
        sweep(&state, block_tree);
        if (state.hold_free)
            insert_free(state.last_free);

        for (Block block; block = list_pop(&state.coalesced);) {
            block_remove_node(&block_tree, block); // bypass tree bounds update
            free(block);
        }

        for (Block block; block = list_pop(&state.munmap);) {
            remove_block(block);
            if (munmap(block->base - block->mmap_offset,
                       block->size + block->mmap_offset) == -1)
                assert_failed("munmap() failed");
            free(block);
        }
    }

    if (heap_size.size <= SIZE_MAX - heap_size.size)
        heap_size.trigger = MAX(1 << 20, heap_size.size * 2);
    else
        heap_size.trigger = heap_size.size;

    hold_stack_shrink();
    hold_mvalue_stack_shrink();
    hold_array_stack_shrink();

#ifndef NDEBUG
    if (block_tree) {
        verify_tree(block_tree);
        verify_heap(block_tree);
    }
#endif
}
