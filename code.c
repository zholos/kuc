/*
    Copyright 2010, 2011 Andrey Zholos

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

#include "code.h"

#include "alloc.h"
#include "apply.h"
#include "verb.h"

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>

#define index index_hide /* index() should be in string.h anyway */
#include <string.h>
#undef index


#ifndef NJIT

//
// Memory allocator for machine code
//

static void* malloc_checked(size_t size) {
    void* memory = malloc(size);
    if (!memory)
        memory_error(size);
    return memory;
}


typedef struct cs_block {
    struct cs_block *next, *prev;
    unsigned char* base;
    size_t size;
    bool free;
    struct {
        void* base;
        size_t size;
    } region;
}* CSBlock;

CSBlock cs_list;


CSBlock cs_find(size_t size) {
    if (size > SIZE_MAX / 2)
        memory_error(size);

    for (CSBlock block = cs_list; block; block = block->next)
        if (block->free && block->size >= size) {
            block->free = 0;
            // change protection for entire region to avoid fragmentation
            if (mprotect(block->region.base, block->region.size,
                         PROT_READ | PROT_WRITE) == -1)
                assert_failed("JIT: mprotect() failed");
            return block;
        }

    size_t alloc = ((1 << 18) + (pagesize-1)) / pagesize * pagesize;
    for (; alloc < size; alloc *= 2);
    void* memory = mmap(NULL, alloc, PROT_READ | PROT_WRITE,
                        MAP_ANON | MAP_PRIVATE, -1, 0);
    if (memory == MAP_FAILED)
        memory_error(alloc);

    CSBlock block = malloc_checked(sizeof *block);
    block->next = cs_list;
    block->prev = NULL;
    if (cs_list)
        cs_list->prev = block;
    cs_list = block;
    block->base = memory;
    block->size = alloc;
    block->free = 0;
    block->region.base = memory;
    block->region.size = alloc;
    return block;
}


void cs_shrink(CSBlock block, size_t size) {
    size = (size + (8-1)) / 8 * 8;
    assert(block->size >= size);
    // all blocks are aligned so we couldn't have found a smaller block

    if (block->next && block->next->free &&
            block->region.base == block->next->region.base) {
        assert(block->next->base == block->base + block->size);
        block->next->base = block->base + size;
        block->next->size += block->size - size;
    } else {
        CSBlock rest = malloc_checked(sizeof *rest);
        rest->next = block->next;
        rest->prev = block;
        if (block->next)
            block->next->prev = rest;
        block->next = rest;
        rest->base = block->base + size;
        rest->size = block->size - size;
        rest->free = 1;
        rest->region = block->region;
    }
    block->size = size;
    if (mprotect(block->region.base, block->region.size,
                 PROT_READ | PROT_EXEC) == -1)
        assert_failed("JIT: mprotect() failed");
}


static void cs_block_coalesce(CSBlock block) {
    assert(block);
    CSBlock rest = block->next;
    if (block->free && rest && rest->free &&
            block->region.base == rest->region.base) {
        assert(rest->base == block->base + block->size);
        block->size += rest->size;
        block->next = rest->next;
        if (block->next)
            block->next->prev = block;
        free(rest);
    }
}


void cs_free(void* base) {
    for (CSBlock block = cs_list; block; block = block->next)
        if (block->base == base) {
            block->free = 1;
            cs_block_coalesce(block);
            if (block->prev && block->prev->region.base == block->region.base) {
                block = block->prev;
                cs_block_coalesce(block);
            }

            if (block->size == block->region.size) {
                if (munmap(block->region.base, block->region.size) == -1)
                    assert_failed("JIT: munmap() failed");
                if (block->next)
                    block->next->prev = block->prev;
                if (block->prev)
                    block->prev->next = block->next;
                else
                    cs_list = block->next;
                free(block);
            }
            return;
        }
    assert_failed("JIT: unknown code fragment released %p", base);
}


//
// JIT state
//

enum var_name {
    var_saved_rbx, // saved reg vars must be in ascending register order
    var_saved_r12,
    var_saved_r13,
    var_saved_r14,
    var_saved_r15,
        var_saved_last = var_saved_r15,
    var_offsets,
    var_verbs,
    var_temps,    // array
    var_literals, // array
    var_upvalues, // array
    var_closure,  // array
        var_count
};

// 0 = scalar, 1 = array
const short j_var_types[var_count] = { 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1 };

enum reg_name {
    rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi,
    r8,  r9,  r10, r11, r12, r13, r14, r15,
        reg_count
};

// 0 = special-purpose, 1 = clobberable, 2 = persistent
const short j_reg_types[reg_count] = { 1, 1, 1, 2, 0, 0, 1, 1,
                                       1, 1, 1, 1, 2, 2, 2, 2 };

struct j_state {
    Code code;
    instr_word ip;
    int pass; // 1 = determine construct uses
              // 2 = count variable uses, enumerate branch targets
              // 3 = allocate variables and generate machine code

    struct branch_target* branch_targets;
    struct branch_forward* branch_forwards;
    instr_word ret; // address of first return instruction or INSTR_LAST
    size_t i_ret; // ip of epilogue in return instruction

    short use_offsets, use_verbs, use_collect,
          use_temps, use_literals, use_upvalues;
          // 0 = no, 1 = maybe, 2 = yes
    size_t persistent_allocs;

    unsigned char* i_instr;
    size_t i_ip;
    int i_frame_free;

    struct j_var {
        size_t uses;
        index mem; // register if >=0, stack frame if <0, reg_count if unused
    } vars[var_count];

    struct j_reg {
        short lock;
        bool var_mem; // used for var
        int var; // cached var
        index ind; // element of array var
        size_t since;
    } regs[reg_count];
};


//
// Machine instructions
//

#define IBYTES(n) i_reserve(s, (n));
#define IBYTE if (s->pass == 3) s->i_instr[s->i_ip++] =

static void i_reserve(struct j_state* s, int count) {
    // fixme: enable after considering implications for upper code size bound
    int nop = s->i_ip % 8 >= 8 ? 8 - s->i_ip % 8 : 0;
    count += nop;

    if (s->pass != 3)
        s->i_ip += count + nop;
    else {
        for (int i = 0; i < nop - 1; i++)
            IBYTE 0x66;
        if (nop)
            IBYTE 0x90;
        //state->jinstr = resize_alloc(
    }
}


static void i_push(struct j_state* s, int reg) {
    assert(reg >= 0);
    IBYTES(2);
    if (reg >= 8)
        IBYTE 0x41;
    IBYTE 0x50 + reg % 8;
}


static void i_leave_ret(struct j_state* s) {
    IBYTES(2);
    IBYTE 0xc9;
    IBYTE 0xc3; // todo: check performance with two-byte ret (0xf3 0xc3)
}


static void i_set_i(struct j_state* s, int reg, uint64_t imm) {
    assert(reg >= 0);
    IBYTES(10);
    if (imm == 0) {
        if (reg >= 8)
            IBYTE 0x45;
        IBYTE 0x33;
        IBYTE 0xc0 + (reg % 8 << 3) + reg % 8;
    } else {
        bool imm64 = imm >> 32;
        if (imm64 || reg / 8)
            IBYTE 0x40 + imm64 * 8 + reg / 8;
        IBYTE 0xb8 + reg % 8;
        for (int i = 0; i < (imm64 ? 8 : 4); i++)
            IBYTE imm >> 8 * i;
    }
}


static void i_copy(struct j_state* s, int dreg, int sreg) {
    assert(dreg >= 0 && sreg >= 0);
    IBYTES(3);
    IBYTE 0x48 + (sreg / 8 << 2) + dreg / 8;
    IBYTE 0x89;
    IBYTE 0xc0 + (sreg % 8 << 3) + dreg % 8;
}


static void i_instr_rm(struct j_state* s, bool prefix, unsigned char opcode,
                       int tail, int reg, int base, int64_t off, size_t size) {
    assert(reg >= 0 && base >= 0);
    assert(size == 8 || size == 4);
    IBYTES(8 + prefix + tail);
    int rex = (size == 8) * 8 + (reg / 8 << 2) + base / 8;
    if (rex)
        IBYTE 0x40 + rex;
    if (prefix)
        IBYTE 0x0f;
    IBYTE opcode;
    bool off0 = off == 0 && base % 8 != rbp;
    bool off8 = off >= -128 && off < 128;
    IBYTE (off0 ? 0x00 : off8 ? 0x40 : 0x80) + (reg % 8 << 3) + base % 8;
    if (base % 8 == rsp)
        IBYTE 0x24;
    if (!off0)
        for (int i = 0; i < (off8 ? 1 : 4); i++)
            IBYTE off >> 8 * i;
}

static void i_load(struct j_state* s,
                   int reg, int base, int64_t off, size_t size) {
    i_instr_rm(s, 0, 0x8b, 0, reg, base, off, size);
}

static void i_load_c(struct j_state* s,
                   int reg, int base, int64_t off, size_t size, int cond) {
    i_instr_rm(s, 1, 0x40 + cond, 0, reg, base, off, size);
}

static void i_load_a(struct j_state* s, int reg, int base, int64_t off) {
    i_instr_rm(s, 0, 0x8d, 0, reg, base, off, 8);
}

static void i_store(struct j_state* s, int base, int64_t off, int reg) {
    i_instr_rm(s, 0, 0x89, 0, reg, base, off, 8);
}

static void i_cmp_m(struct j_state* s,
                    int base, int64_t off, size_t size, int reg) {
    i_instr_rm(s, 0, 0x39, 0, reg, base, off, size);
}

static void i_store_i(struct j_state* s,
               int base, int64_t off, size_t size, int32_t imm) {
    i_instr_rm(s, 0, 0xc7, 4, 0, base, off, size);
    for (int i = 0; i < 4; i++)
        IBYTE imm >> 8 * i;
}

static void i_sub_mi(struct j_state* s,
              int base, int64_t off, size_t size, int32_t imm) {
    bool imm8 = imm >= -128 && imm < 128;
    i_instr_rm(s, 0, imm8 ? 0x83 : 0x81, 0, 5, base, off, size);
    IBYTES(4);
    for (int i = 0; i < (imm8 ? 1 : 4); i++)
        IBYTE imm >> 8 * i;
}

static void i_dec_m(struct j_state* s, int base, int64_t off) {
    i_instr_rm(s, 0, 0xff, 0, 1, base, off, 8);
}

static void i_call_m(struct j_state* s, int base, int64_t off) {
    i_instr_rm(s, 0, 0xff, 0, 2, base, off, 4); // size 8 implied
}


static void i_instr_ri(struct j_state* s,
                       bool wide, int add, int reg, int32_t imm) {
    assert(reg >= 0);
    IBYTES(7);
    if (wide || reg >= 8)
        IBYTE 0x40 + wide * 8 + reg / 8;
    bool imm8 = imm >= -128 && imm < 128;
    IBYTE imm8 ? 0x83 : 0x81;
    IBYTE 0xc0 + (add << 3) + reg % 8;
    for (int i = 0; i < (imm8 ? 1 : 4); i++)
        IBYTE imm >> 8 * i;
}

static void i_add_i(struct j_state* s, int reg, int32_t imm) {
    i_instr_ri(s, 1, 0, reg, imm);
}

static void i_sub_i(struct j_state* s, int reg, int32_t imm) {
    i_instr_ri(s, 1, 5, reg, imm);
}

static void i_and_i(struct j_state* s, int reg, int32_t imm) {
    i_instr_ri(s, 0, 4, reg, imm);
}

static void i_cmp_id(struct j_state* s, int reg, int32_t imm) {
    i_instr_ri(s, 0, 7, reg, imm);
}


static void i_cmp_d(struct j_state* s, int dreg, int sreg) {
    IBYTES(3);
    if (dreg >= 8 || sreg >= 8)
        IBYTE 0x40 + (dreg / 8 << 2) + sreg / 8;
    IBYTE 0x3b;
    IBYTE 0xc0 + (dreg % 7 << 3) + sreg % 8;
}


static void i_test_i(struct j_state* s, int reg, uint32_t imm) {
    // todo: check
    IBYTES(7);
    bool imm8 = imm < 256;
    if (!imm8 || reg >= 8)
        IBYTE 0x40 + !imm8 * 8 + reg / 8;
    IBYTE imm8 ? 0xf6 : 0xf7;
    IBYTE 0xc0 + reg % 8;
    for (int i = 0; i < (imm8 ? 1 : 4); i++)
        IBYTE imm >> 8 * i;
}


static void i_inc(struct j_state* s, int reg) {
    assert(reg >= 0);
    IBYTES(3);
    IBYTE 0x48 + reg / 8;
    IBYTE 0xff;
    IBYTE 0xc0 + (0 << 3) + reg % 8;
}


static void i_cdqe(struct j_state* s) {
    IBYTES(2);
    IBYTE 0x48;
    IBYTE 0x98;
}


static void i_test_al(struct j_state* s) {
    IBYTES(2);
    IBYTE 0x84;
    IBYTE 0xc0;
}


static void i_shl_eax_1(struct j_state* s) {
    IBYTES(2);
    IBYTE 0xd1;
    IBYTE 0xe0;
}


static void i_setc_al(struct j_state* s, int cond) {
    IBYTES(3);
    IBYTE 0x0f;
    IBYTE 0x90 + cond;
    IBYTE 0xc0;
}


enum cond {
    c_o, c_no, c_b, c_ae, c_z, c_nz, c_be, c_a,
    c_s, c_ns, c_p, c_np, c_l, c_ge, c_le, c_g
};

static size_t i_jmp(struct j_state* s, size_t to, bool off8, int cond) {
    IBYTES(6);
    int32_t off = 0;
    if (to) {
        assert(to <= s->i_ip);
        off = -(s->i_ip - to);
        off8 = off - 2 >= -128;
        off -= off8 ? 2 : 5 + (cond >= 0);
    }
    if (!off8 && cond >= 0)
        IBYTE 0x0f;
    IBYTE cond >= 0 ? (off8 ? 0x70 : 0x80) + cond : off8 ? 0xeb : 0xe9;
    for (int i = 0; i < (off8 ? 1 : 4); i++)
        IBYTE off >> 8 * i;
    return s->i_ip;
}


static void i_jmp_off(struct j_state* s, bool off8, size_t where) {
    int off = where <= s->i_ip ?  (int)(s->i_ip - where)
                               : -(int)(where - s->i_ip);
    if (off8 && !(off >= -128 && off < 128))
        assert_failed("JIT: target too far for short jump");
    if (s->pass == 3)
        for (int i = 0; i < (off8 ? 1 : 4); i++)
            s->i_instr[where - (off8 ? 1 : 4) + i] = off >> 8 * i;
}


static void i_call(struct j_state* s, size_t to) {
    int off = to <= s->i_ip + 5 ? -(int)((s->i_ip + 5) - to)
                                :  (int)(to - (s->i_ip + 5));
    IBYTES(5);
    IBYTE 0xe8;
    for (int i = 0; i < 4; i++)
        IBYTE off >> 8 * i;
}


//
// Intermediate form
//

struct j_offsets {
    const struct verb_run* verbs_run;
    Value (*call_binary)(Value, Value, Value);
    Value (*run)(Value*);
    Value (*call)(Value, index, const Value*);
    Value (*project)(Value, index, const Value*);
    bool (*as_condition)(Value);
    index (*as_index)(Value);
    struct hold_array_stack* hold_array_stack;
    void (*hold_array_stack_grow)();
    struct heap_size* heap_size;
    void* (*alloc)(size_t, int alloc_type);
    void (*collect)();
    Value untyped_null;
} j_offsets = {
    verbs_run,
    call_binary,
    run,
    call,
    project,
    as_condition_no_shortcut,
    as_index,
    &hold_array_stack,
    hold_array_stack_grow,
    &heap_size,
    alloc,
    collect,
    (Value)&untyped_null
};


#define OFF(aggr, member) offsetof(struct aggr, member)
#define SIZ(aggr, member) sizeof ((struct aggr*)NULL)->member
#define OFFSIZ(aggr, member) OFF(aggr, member), SIZ(aggr, member)


static void j_enter(struct j_state* s, index frame_size) {
    i_push(s, rbp);
    i_copy(s, rbp, rsp);
    if (frame_size)
        i_sub_i(s, rsp, frame_size * 8);
}


static void j_cache(struct j_state* s, int reg, int var, index ind) {
    if (s->pass == 3) {
        s->regs[reg].var = var;
        s->regs[reg].ind = ind;
        s->regs[reg].since = s->i_ip;
    }
}


static void j_cache_flush(struct j_state* s) {
    if (s->pass == 3)
        for (int i = 0; i < reg_count; i++) {
            if (s->regs[i].lock > s->regs[i].var_mem)
                assert_failed("JIT: locked machine register at branch target");
            s->regs[i].var = -1;
        }
}


// kind:
//   -1 = temporary allocation: next alloc_reg may reuse
//   -2 = persistent allocation: prefer non-clobberable registers

static int j_alloc_reg(struct j_state* s, int kind) {
    assert(kind == -1 || kind == -2);
    if (kind == -2)
        s->persistent_allocs++;
    int reg = -1;
    for (int i = 0; i < reg_count; i++)
        if (j_reg_types[i] && !s->regs[i].lock && (reg < 0 ||
                kind == -2 && j_reg_types[reg] == 1 && j_reg_types[i] == 2 ||
                s->regs[reg].var >= 0 && (s->regs[i].var < 0 ||
                    s->regs[reg].since > s->regs[i].since)))
            reg = i;
    if (reg < 0)
        assert_failed("JIT: no free machine registers");
    s->regs[reg].var = -1;
    return reg;
}


static void j_lock_reg(struct j_state* s, int reg) {
    assert(reg >= 0);
    if (s->regs[reg].lock)
        assert_failed("JIT: required machine register in use");
    s->regs[reg].lock = 1;
}


static void j_overlock_reg(struct j_state* s, int reg) {
    assert(reg >= 0);
    s->regs[reg].lock++;
}


static void j_free_reg(struct j_state* s, int reg) {
    assert(reg >= 0);
    if (!s->regs[reg].lock)
        assert_failed("JIT: unlocking unlocked register");
    s->regs[reg].lock--;
}


static int j_load_var(struct j_state* s, int reg, int var, index ind) {
    assert(j_var_types[var] == 1 || ind < 0);

    if (s->vars[var].mem == reg_count)
        assert_failed("JIT: accessing unallocated variable");

    if (ind < 0)
        s->vars[var].uses++;

    if (s->vars[var].mem < 0 || ind >= 0) {
        for (int i = 0; i < reg_count; i++)
            if (s->regs[i].var == var && s->regs[i].ind == ind) {
                if (reg == i)
                    ;
                else if (reg < 0)
                    reg = i;
                else
                    i_copy(s, reg, i);
                goto done;
            }

        if (ind >= 0) {
            int base = j_load_var(s, -1, var, -1);
            if (reg < 0) {
                j_overlock_reg(s, base);
                reg = j_alloc_reg(s, reg);
                j_free_reg(s, base);
            }
            i_load(s, reg, base, ind * 8, 8);
        } else {
            if (reg < 0)
                reg = j_alloc_reg(s, reg);
            i_load(s, reg, rbp, s->vars[var].mem * 8, 8);
        }
    } else {
        if (s->vars[var].mem == reg)
            ;
        else if (reg < 0)
            reg = s->vars[var].mem;
        else
            i_copy(s, reg, var);
    }

done:
    j_cache(s, reg, var, ind);
    return reg;
}


static void j_store_var(struct j_state* s, int var, index ind, int reg) {
    assert(j_var_types[var] == 1 || ind < 0);

    if (s->vars[var].mem == reg_count)
        assert_failed("JIT: accessing unallocated variable");

    if (ind < 0)
        s->vars[var].uses++;

    if (ind >= 0) {
        j_overlock_reg(s, reg);
        int base = j_load_var(s, -1, var, -1);
        j_free_reg(s, reg);
        i_store(s, base, ind * 8, reg);
    } else if (s->vars[var].mem < 0)
        i_store(s, rbp, s->vars[var].mem * 8, reg);
    else if (s->vars[var].mem != reg)
        i_copy(s, s->vars[var].mem, reg);
    j_cache(s, reg, var, ind);
}


static void j_set_var(struct j_state* s, int var, uint64_t imm) {
    s->vars[var].uses++;

    if (s->vars[var].mem < 0) {
        int reg = j_alloc_reg(s, -1);
        j_lock_reg(s, reg);
        i_set_i(s, reg, imm);
        j_store_var(s, var, -1, reg);
        j_free_reg(s, reg);
    } else
        i_set_i(s, s->vars[var].mem, imm);
}


static int j_load_slot(struct j_state* s, int reg, instr_word slot) {
    switch (slot / INSTR_PART) {
    case 0:
        s->use_temps = 2;
        return j_load_var(s, reg, var_temps, slot);
    case 1:
        return j_load_var(s, reg, var_closure, slot % INSTR_PART);
    case 2:
        s->use_upvalues = 2;
        return j_load_var(s, reg, var_upvalues, slot % INSTR_PART);
    default:
        s->use_literals = 2;
        return j_load_var(s, reg, var_literals, slot % INSTR_PART);
    }
}


static void j_store_slot(struct j_state* s, instr_word slot, int reg) {
    switch (slot / INSTR_PART) {
    case 0:
        s->use_temps = 2;
        j_store_var(s, var_temps, slot, reg);
        break;
    case 1:
        j_store_var(s, var_closure, slot % INSTR_PART, reg);
        break;
    case 2:
        s->use_upvalues = 2;
        j_store_var(s, var_upvalues, slot % INSTR_PART, reg);
        break;
    default:
        s->use_literals = 2;
        j_store_var(s, var_literals, slot % INSTR_PART, reg); // why not?
    }
}


static void j_clobber(struct j_state* s) {
    // this doesn't allocate registers, so locks on clobberable registers may
    // be released for the duration of this call, and reacquired afterwards for
    // the values to be reloaded into the same registers
    for (int i = 0; i < reg_count; i++)
        if (j_reg_types[i] == 1) {
            if (s->regs[i].lock)
                assert_failed("JIT: locked machine register clobbered by call");
            s->regs[i].var = -1;
        }
}


static void j_call_m(struct j_state* s, int var, int64_t off, int args) {
    int offsets = j_load_var(s, -1, var, -1);
    assert(args <= 3);
    if (args > 0)
        j_free_reg(s, rdi);
    if (args > 1)
        j_free_reg(s, rsi);
    if (args > 2)
        j_free_reg(s, rdx);
    i_call_m(s, offsets, off);
    j_clobber(s);
}


#define STATIC_ASSERT(name, cond) typedef char check_##name[-1+2*(int)(cond)];

// type and vector field of value_func should both be in the first doubleword,
// so we assign them together

STATIC_ASSERT(layout_func,
    OFF(value_func, type_func)   + SIZ(value_func, type_func)   <= 4 &&
    OFF(value_func, vector_func) + SIZ(value_func, vector_func) <= 4 &&
    OFF(value_func, func) >= 4);


static void j_prologue(struct j_state* s) {
    int frame_size = 0;
    for (int i = 0; i < var_count; i++)
        if (frame_size < -s->vars[i].mem)
            frame_size = -s->vars[i].mem;

    int64_t closure_off = 0; // initialized to make compiler happy
    if (s->code->closed) {
        frame_size += (sizeof(struct value_func) + (8-1)) / 8;
        closure_off = (int64_t)-frame_size * 8;
    }

    if (s->i_frame_free = frame_size % 2)
        frame_size++; // achieve ABI-mandated 16-byte alignment of rsp
    if (s->pass != 3)
        s->i_frame_free = 0; // larger frame potentially uses more code

    j_enter(s, frame_size);

    j_lock_reg(s, rdi); // input argument
    j_store_var(s, var_saved_rbx, -1, rbx);
    j_store_var(s, var_saved_r12, -1, r12);
    j_store_var(s, var_saved_r13, -1, r13);
    j_store_var(s, var_saved_r14, -1, r14);
    j_store_var(s, var_saved_r15, -1, r15);
    j_free_reg(s, rdi);
    j_cache_flush(s); // none of these vars should be cached in these registers
                      // because the registers are used for other vars

    if (s->use_temps)
        j_store_var(s, var_temps, -1, rdi);

    if (s->use_offsets)
        j_set_var(s, var_offsets, (uint64_t)&j_offsets);

    if (s->code->closed) {
        i_store_i(s, rbp, closure_off, 4,
                  type_func << CHAR_BIT * OFF(value_func, type_func) |
                  0         << CHAR_BIT * OFF(value_func, vector_func));
        i_store_i(s, rbp, closure_off + OFF(value_func, func.code), 4, 0);
                  // note: NULL is 0 on this platform

        j_lock_reg(s, rdi);
        j_lock_reg(s, rsi);
        i_set_i(s, rdi, (uint64_t)s->code->closed * 8);
        i_set_i(s, rsi, alloc_modifyable);
        s->use_offsets = 2;
        j_call_m(s, var_offsets, OFF(j_offsets, alloc), 2);

        i_store(s, rbp, closure_off + OFF(value_func, func.upvalues), rax);
        j_store_var(s, var_closure, -1, rax);

        int closure = j_alloc_reg(s, -1);
        i_load_a(s, closure, rbp, closure_off);
        s->use_temps = 2;
        j_store_var(s, var_temps, 1 + s->code->args, closure);
    }

    if (s->use_collect) {
        int offsets = j_load_var(s, -2, var_offsets, -1);
        j_overlock_reg(s, offsets);

        int hold_array = j_alloc_reg(s, -2);
        j_lock_reg(s, hold_array);
        i_load(s, hold_array, offsets, OFF(j_offsets, hold_array_stack), 8);

        int hot1 = j_alloc_reg(s, -2);
        int hot2 = 0; // initialized to make compiler happy
        j_lock_reg(s, hot1);
        i_load(s, hot1, hold_array, OFF(hold_array_stack, hot), 8);

        i_cmp_m(s, hold_array, OFFSIZ(hold_array_stack, end), hot1);
        size_t j;
        if (!s->code->closed)
            j = i_jmp(s, 0, 0, c_nz);
        else {
            size_t k = i_jmp(s, 0, 0, c_z);

            hot2 = j_alloc_reg(s, -2);
            j_lock_reg(s, hot2);
            i_load_a(s, hot2, hot1, sizeof(struct hold_array_stack_item));
            i_cmp_m(s, hold_array, OFFSIZ(hold_array_stack, end), hot2);
            j = i_jmp(s, 0, 0, c_nz);

            i_jmp_off(s, 0, k);
        }

        i_call_m(s, offsets, OFF(j_offsets, hold_array_stack_grow));
        j_free_reg(s, offsets); // release and reload if they get clobbered
        j_free_reg(s, hold_array);
        j_free_reg(s, hot1); // reload always because it's changed by grow
        if (s->code->closed)
            j_free_reg(s, hot2);
        j_clobber(s);
        j_overlock_reg(s, offsets);
        j_lock_reg(s, hold_array);
        j_lock_reg(s, hot1);
        if (s->code->closed)
            j_lock_reg(s, hot2);
        if (j_reg_types[offsets] == 1)
            j_load_var(s, offsets, var_offsets, -1);
        if (j_reg_types[hold_array] == 1)
            i_load(s, hold_array, offsets, OFF(j_offsets, hold_array_stack), 8);
        i_load(s, hot1, hold_array, OFF(hold_array_stack, hot), 8);
        if (s->code->closed) {
            i_load_a(s, hot2, hot1, sizeof(struct hold_array_stack_item));
        }

        i_jmp_off(s, 0, j);
        j_free_reg(s, offsets);
        j_free_reg(s, hold_array);

        i_store_i(s, hot1, OFFSIZ(hold_array_stack_item, n), s->code->frame);
        int temps = j_load_var(s, -1, var_temps, -1);
        i_store(s, hot1, OFF(hold_array_stack_item, p), temps);
        if (s->code->closed) {
            i_store_i(s, hot2, OFFSIZ(hold_array_stack_item, n), s->code->closed);
            int closure = j_load_var(s, -1, var_closure, -1);
            i_store(s, hot2, OFF(hold_array_stack_item, p), closure);
            j_free_reg(s, hot1);
            hot1 = hot2;
        }
        i_add_i(s, hot1, sizeof(struct hold_array_stack_item));
        i_store(s, hold_array, OFF(hold_array_stack, hot), hot1);
        j_free_reg(s, hot1);
    }

    if (s->use_literals)
        j_set_var(s, var_literals, (uint64_t)s->code->literals);
    if (s->use_verbs)
        j_set_var(s, var_verbs, (uint64_t)&verbs_run);

    if (s->use_upvalues) {
        int self = j_load_var(s, -1, var_temps, 0);
        if (s->vars[var_upvalues].mem < 0) {
            j_overlock_reg(s, self);
            int upvalues = j_alloc_reg(s, -1);
            j_free_reg(s, self);
            i_load(s, upvalues, self, OFF(value_func, func.upvalues), 8);
            j_store_var(s, var_upvalues, -1, upvalues);
        } else
            i_load(s, s->vars[var_upvalues].mem,
                   self, OFF(value_func, func.upvalues), 8);
    }
}


static void j_epilogue(struct j_state* s) {
    j_lock_reg(s, rax);

    if (s->use_collect) {
        int offsets = j_load_var(s, -1, var_offsets, -1);
        j_overlock_reg(s, offsets);

        int hold_array = j_alloc_reg(s, -1);
        j_free_reg(s, offsets);
        i_load(s, hold_array, offsets, OFF(j_offsets, hold_array_stack), 8);
        i_sub_mi(s, hold_array, OFFSIZ(hold_array_stack, hot),
                                (s->code->closed ? 2 : 1) *
                                    sizeof(struct hold_array_stack_item));
    }

    j_load_var(s, rbx, var_saved_rbx, -1);
    j_load_var(s, r12, var_saved_r12, -1);
    j_load_var(s, r13, var_saved_r13, -1);
    j_load_var(s, r14, var_saved_r14, -1);
    j_load_var(s, r15, var_saved_r15, -1);
    j_free_reg(s, rax);
    i_leave_ret(s);
}


static void j_reached_collect(struct j_state* s) {
    if (s->pass == 3 && !s->use_collect)
        assert_failed("JIT: unexpectedly reached collector");
    s->use_collect = 2;
}


static void j_check_collect(struct j_state* s) {
    j_reached_collect(s);

    int offsets = j_load_var(s, -1, var_offsets, -1);
    j_overlock_reg(s, offsets);

    int heap_size = j_alloc_reg(s, -1);
    j_lock_reg(s, heap_size);
    i_load(s, heap_size, offsets, OFF(j_offsets, heap_size), 8);
    j_free_reg(s, offsets);

    int size = j_alloc_reg(s, -1);
    i_load(s, size, heap_size, OFF(heap_size, size), 8);

    i_cmp_m(s, heap_size, OFFSIZ(heap_size, trigger), size);
    j_free_reg(s, heap_size);
    size_t j = i_jmp(s, 0, 1, c_ae);

    // since this is an unlikely path, try to preserve rax inside it
    if (s->regs[rax].var) {
        int saved = j_alloc_reg(s, -2);
        if (j_reg_types[saved] == 2) {
            j_lock_reg(s, saved);
            struct j_reg reg_rax = s->regs[rax];
            i_copy(s, saved, rax);
            j_call_m(s, var_offsets, OFF(j_offsets, collect), 0);
            j_free_reg(s, saved);
            i_copy(s, rax, saved);
            s->regs[rax] = reg_rax;
            goto called;
        }
    }

    j_call_m(s, var_offsets, OFF(j_offsets, collect), 0);
called:
    i_jmp_off(s, 1, j);
}


struct branch_target {
    struct branch_target* next;
    instr_word ip;
    size_t i_ip;
} branch_target_end = { NULL, INSTR_LAST };


struct branch_forward {
    struct branch_forward* next;
    instr_word ip;
    size_t i_off;
};


static void j_branch(struct j_state* s, instr_word ip, int cond) {
    switch (s->pass) {
    case 2: {
        struct branch_target** target = &s->branch_targets;
        for (; (*target)->ip < ip; target = &(*target)->next);
        if ((*target)->ip != ip) {
            struct branch_target* next = *target;
            *target = malloc_checked(sizeof **target);
            (*target)->next = next;
            (*target)->ip = ip;
        }
        i_jmp(s, 0, 0, cond);
        break;
    }
    case 3:
        if (ip <= s->ip) {
            struct branch_target* target = s->branch_targets;
            for (; target->ip < ip; target = target->next);
            assert(target->ip == ip);
            i_jmp(s, target->i_ip, 0, cond);
        } else {
            struct branch_forward* forward = malloc_checked(sizeof *forward);
            forward->next = s->branch_forwards;
            forward->ip = ip;
            forward->i_off = i_jmp(s, 0, 0, cond);
            s->branch_forwards = forward;
        }
    }
}


// the jnz instruction code expects a very specific layout of bool and int

STATIC_ASSERT(layout_bool,
    OFF(value_bool, type_bool)   == 0 && SIZ(value_bool, type_bool)   == 2 &&
    OFF(value_bool, vector_bool) == 2 && SIZ(value_bool, vector_bool) == 1 &&
    OFF(value_bool, _bool)       == 3 && SIZ(value_bool, _bool)       == 1)

STATIC_ASSERT(layout_int,
    OFF(value_int, type_int)   == 0 && SIZ(value_int, type_int)   == 2 &&
    OFF(value_int, vector_int) == 2 && SIZ(value_int, vector_int) == 1 &&
    OFF(value_int, _int)       >= 4 && SIZ(value_int, _int)       == 4)


// it also expect certain numerical values for constants

STATIC_ASSERT(values_typ, type_bool == 1 && type_int == 3)
STATIC_ASSERT(values_int, int_null == 0x80000000)


static void j_jnz(struct j_state* s, instr_word ip, instr_word cond) {
    j_load_slot(s, rdi, cond);
    j_lock_reg(s, rdi);

#ifndef NSHORTCUT
    j_lock_reg(s, rax);

    int dword = j_alloc_reg(s, -1);
    j_lock_reg(s, dword);
    int type = j_alloc_reg(s, -1);
    j_free_reg(s, dword);
    j_free_reg(s, rax);

    i_load(s, dword, rdi, 0, 4);
    i_set_i(s, rax, 0);
    i_copy(s, type, dword);
    i_and_i(s, type, 0x00fffffd); // mask out second bit ...
    i_cmp_id(s, type, 1);         // ... which is the difference between 1 and 3
    size_t j_call = i_jmp(s, 0, 1, c_nz);

    i_cmp_d(s, dword, type); // bool type word is not modified
    i_setc_al(s, c_g);

    i_test_i(s, dword, 2);
    i_load_c(s, rax, rdi, OFFSIZ(value_int, _int), 5);

    i_shl_eax_1(s);
    j_branch(s, ip, c_z);
    size_t j_done = i_jmp(s, 0, 1, -1);

    i_jmp_off(s, 1, j_call);
    s->use_offsets = 2;
    j_call_m(s, var_offsets, OFF(j_offsets, as_condition), 1);
    i_test_al(s);
    j_branch(s, ip, c_z);

    i_jmp_off(s, 1, j_done);
#else
    s->use_offsets = 2;
    j_call_m(s, var_offsets, OFF(j_offsets, as_condition), 1);
    i_test_al(s);
    j_branch(s, ip, c_z);
#endif
}


static Code j_reg_code(struct j_state* s, instr_word f) {
    if (f == 0)
        return s->code;
    if (f >= 3*INSTR_PART) {
        Value func = s->code->literals[f - 3*INSTR_PART];
        if (func->type == type_func)
            return func->func.code;
    }
    return NULL;
}


static void j_run_head(struct j_state* s, Code f_code) {
    int frame = (f_code->frame - s->i_frame_free + 1) / 2 * 2;
    i_sub_i(s, rsp, frame * 8); // fixme: check for overflow
}


static void j_run_load(struct j_state* s, index base, index n) {
    for (index i = 0; i <= n;) {
        int batch = i < n - 2 ? 2 : n - i + 1;
        int arg[3];
        for (int j = 0; j < batch; j++) {
            arg[j] = j_load_slot(s, -1, s->code->instr[s->ip+base+i+j]);
            j_overlock_reg(s, arg[j]);
        }
        for (int j = 0; j < batch; j++) {
            j_free_reg(s, arg[j]);
            i_store(s, rsp, (int64_t)(i + j) * 8, arg[j]);
        }
        i += batch;
    }
}


static void j_run_tail(struct j_state* s, Code f_code) {
    int frame = (f_code->frame - s->i_frame_free + 1) / 2 * 2;
                // must match j_run_head definition

    i_copy(s, rdi, rsp);
    if (f_code == s->code) {
        i_call(s, 0);
        j_clobber(s);
    } else {
        j_lock_reg(s, rdi);
        s->use_offsets = 2;
        j_call_m(s, var_offsets, OFF(j_offsets, run), 1);
    }
    j_store_slot(s, s->code->instr[s->ip+1], rax);
    i_add_i(s, rsp, frame * 8); // fixme: check for overflow

    j_reached_collect(s);
}


// index should be size 4 or 8 (for verb_init_counter clause)

STATIC_ASSERT(index_size, sizeof(index) == 4 || sizeof(index) == 8)


#define MAX(x, y) ((x) > (y) ? (x) : (y))

static void j_compile(struct j_state* s) {
    const instr_word *const instr = s->code->instr;
    struct branch_target* target = s->branch_targets;

    j_prologue(s);

    bool just_collected = 0;
    instr_word end = 0;
    for (s->ip = 0; s->ip <= end;) {
        bool collect = 0;

        for (struct branch_forward** forward = &s->branch_forwards; *forward;)
            if ((*forward)->ip == s->ip) {
                i_jmp_off(s, 0, (*forward)->i_off);
                struct branch_forward* next = (*forward)->next;
                free(*forward);
                *forward = next;
                j_cache_flush(s);
            } else
                forward = &(*forward)->next;

        if (s->ip == target->ip) {
            target->i_ip = s->i_ip;
            target = target->next;
            j_cache_flush(s);
        }

        switch (instr[s->ip] / INSTR_PART) {
        case 0: {
            unsigned verb = instr[s->ip];
            switch (verb) {
            case verb_at: {
                Code f_code = j_reg_code(s, instr[s->ip+2]);
                if (f_code && f_code->args == 1) {
                    j_run_head(s, f_code);
                    j_run_load(s, 2, 1);
                    j_run_tail(s, f_code);
                    collect = 1;
                    break;
                }
                // falls through
            }
            default:
                s->use_verbs = 2;
                j_load_slot(s, rdi, instr[s->ip+2]);
                j_lock_reg(s, rdi);
                j_load_slot(s, rsi, instr[s->ip+3]);
                j_lock_reg(s, rsi);
                j_call_m(s, var_verbs, (int64_t)sizeof *verbs_run * verb +
                                       offsetof(struct verb_run, binary), 2);
                j_store_slot(s, instr[s->ip+1], rax);
                collect = verbs_run[verb].binary_collect;
            }
            s->ip += 4;
            end = MAX(end, s->ip);
            break;
        }
        case 1: {
            unsigned verb = instr[s->ip] % INSTR_PART;
            switch (verb) {
            case verb_null: {
                int reg = j_load_slot(s, -1, instr[s->ip+2]);
                j_store_slot(s, instr[s->ip+1], reg);
                break;
            }
            case verb_init_counter: {
                j_load_slot(s, rdi, instr[s->ip+2]);
                j_lock_reg(s, rdi);
                j_call_m(s, var_offsets, OFF(j_offsets, as_index), 1);
                if (sizeof(index) == 4) // size checked statically above
                    i_cdqe(s);
                i_inc(s, rax);
                j_store_slot(s, instr[s->ip+1], rax);
                break;
            }
            case verb_dot: {
                Code f_code = j_reg_code(s, instr[s->ip+2]);
                if (f_code && f_code->args == 1) {
                    j_run_head(s, f_code);

                    int func = j_load_slot(s, -1, instr[s->ip+2]);
                    j_overlock_reg(s, func);

                    s->use_offsets = 2;
                    int offsets = j_load_var(s, -1, var_offsets, -1);
                    j_overlock_reg(s, offsets);
                    int null = j_alloc_reg(s, -1);
                    j_free_reg(s, offsets);
                    j_free_reg(s, func);
                    i_load(s, null, offsets, OFF(j_offsets, untyped_null), 8);

                    i_store(s, rsp, 0 * 8, func);
                    i_store(s, rsp, 1 * 8, null);

                    j_run_tail(s, f_code);
                    collect = 1;
                    break;
                }
                // falls through
            }
            default:
                s->use_verbs = 2;
                j_load_slot(s, rdi, instr[s->ip+2]);
                j_lock_reg(s, rdi);
                j_call_m(s, var_verbs, (int64_t)sizeof *verbs_run * verb +
                                       offsetof(struct verb_run, unary), 1);
                j_store_slot(s, instr[s->ip+1], rax);
                collect = verbs_run[verb].unary_collect;
            }
            s->ip += 3;
            end = MAX(end, s->ip);
            break;
        }
        case 2: {
            int n = instr[s->ip] % (INSTR_PART/2) + 2;
            bool partial = instr[s->ip] % INSTR_PART / (INSTR_PART/2);

            Code f_code = j_reg_code(s, instr[s->ip+2]);
            if (f_code && !partial && f_code->args == n) {
                j_run_head(s, f_code);
                j_run_load(s, 2, n);
                j_run_tail(s, f_code);
            } else if (n == 2 && !partial) {
                j_load_slot(s, rdi, instr[s->ip+2]);
                j_lock_reg(s, rdi);
                j_load_slot(s, rsi, instr[s->ip+3]);
                j_lock_reg(s, rsi);
                j_load_slot(s, rdx, instr[s->ip+4]);
                j_lock_reg(s, rdx);
                s->use_offsets = 2;
                j_call_m(s, var_offsets, OFF(j_offsets, call_binary), 3);
                j_store_slot(s, instr[s->ip+1], rax);
            } else {
                int args = (n - s->i_frame_free + 1) / 2 * 2;
                i_sub_i(s, rsp, args * 8); // fixme: check for overflow

                j_run_load(s, 3, n-1);
                j_load_slot(s, rdi, instr[s->ip+2]);
                j_lock_reg(s, rdi);
                i_set_i(s, rsi, n);
                j_lock_reg(s, rsi);
                i_copy(s, rdx, rsp);
                j_lock_reg(s, rdx);
                s->use_offsets = 2;
                j_call_m(s, var_offsets, partial ? OFF(j_offsets, project)
                                                 : OFF(j_offsets, call), 3);
                i_add_i(s, rsp, args * 8);
                j_store_slot(s, instr[s->ip+1], rax);
            }

            s->ip += 3 + n;
            end = MAX(end, s->ip);

            collect = 1;
            break;
        }
        default:
            switch (instr[s->ip] % INSTR_PART) {
            case 0:
                j_load_slot(s, rax, instr[s->ip+1]);
                if (s->ret == INSTR_LAST)
                    s->ret = s->ip;
                if (s->ip == s->ret) {
                    s->i_ret = s->i_ip;
                    j_epilogue(s);
                } else
                    i_jmp(s, s->i_ret, 0, -1);
                s->ip += 2;
                break;
            case 1:
                j_branch(s, instr[s->ip+1], -1);
                end = MAX(end, instr[s->ip+1]);
                s->ip += 2;
                break;
            case 2: {
                j_jnz(s, instr[s->ip+1], instr[s->ip+2]);
                end = MAX(end, instr[s->ip+1]);
                s->ip += 3;
                end = MAX(end, s->ip);
                break;
            }
            case 3:
                if (!just_collected)
                    j_check_collect(s);

                assert(instr[s->ip+2] < INSTR_PART);
                s->use_temps = 2;
                int temps = j_load_var(s, -1, var_temps, -1);
                i_dec_m(s, temps, (int64_t)instr[s->ip+2] * 8);
                j_branch(s, instr[s->ip+1], c_g);

                end = MAX(end, instr[s->ip+1]);
                s->ip += 3;
                end = MAX(end, s->ip);
                break;
            default:
                assert_failed("unknown instruction");
            }
        }

        if (collect && s->ip <= end && instr[s->ip] == 3*INSTR_PART + 0) {
            j_reached_collect(s);
            collect = 0; // don't bother collecting just before returning
        }

        if (collect)
            j_check_collect(s);
        just_collected = collect;
    }

    j_cache_flush(s);
}


static void jit(Code code) {
    struct j_state state;
    state.code = code;
    state.branch_targets = &branch_target_end;
    state.branch_forwards = NULL;
    state.ret = INSTR_LAST;

    state.use_offsets = 1;
    state.use_verbs = 1;
    state.use_collect = 1;
    state.use_temps = 1;
    state.use_literals = 1;
    state.use_upvalues = 1;
    state.persistent_allocs = 0;

    for (int i = 0; i < var_count; i++) {
        state.vars[i].uses = 0;
        state.vars[i].mem = -1 - i;
            // memory variables use more instruction bytes
    }

    for (int i = 0; i < reg_count; i++) {
        state.regs[i].lock = 0;
        state.regs[i].var_mem = 0;
        state.regs[i].var = -1;
    }

    state.pass = 1;
    state.i_instr = NULL;
    state.i_ip = 0;
    j_compile(&state);

    if (state.use_collect == 2)
        state.use_offsets = 2;
    if (state.use_collect == 2 || state.use_upvalues == 2)
        state.use_temps = 2;

    state.use_offsets--;
    state.use_verbs--;
    state.use_collect--;
    state.use_temps--;
    state.use_literals--;
    state.use_upvalues--;
    state.persistent_allocs = 0;

    for (int i = 0; i < var_count; i++)
        state.vars[i].uses = 0;

    state.pass = 2;
    state.i_ip = 0;
    j_compile(&state);

    for (int i = 0; i < reg_count; i++) {
        // work in reverse order for upper registers because r12- and r13-based
        // memory accesses sometimes require more bytes to encode
        int reg = i < reg_count / 2 ? i : (reg_count - 1) - (i - reg_count / 2);
        if (j_reg_types[reg] == 2) {
            int var = var_saved_last + 1;
            for (int j = var + 1; j < var_count; j++)
                if (state.vars[var].mem >= 0 || state.vars[j].mem < 0 &&
                        state.vars[j].uses > state.vars[var].uses)
                    var = j;
            if (state.vars[var].mem >= 0 || state.vars[var].uses < 3)
                break;
            state.vars[var].mem = reg;
            state.regs[reg].lock = 1;
            state.regs[reg].var_mem = 1;
        }
    }

    if (!state.persistent_allocs) {
        int reg = 0;
        for (int i = 0; i <= var_saved_last; i++) {
            for (; j_reg_types[reg] != 2; reg++);
            if (!state.regs[reg].lock &&
                    state.vars[i].uses && state.vars[i].mem < 0) {
                state.vars[i].mem = reg;
                state.regs[reg].lock = 1;
                state.regs[reg].var_mem = 1;
            }
            reg++;
        }
    }

    for (int i = 0, frame = 0; i < var_count; i++) {
        if (!state.vars[i].uses)
            state.vars[i].mem = reg_count;
        else if (state.vars[i].mem < 0 && state.vars[i].uses)
            state.vars[i].mem = --frame;
        state.vars[i].uses = 0;
    }

    state.pass = 3;
    CSBlock block = cs_find(state.i_ip);
    state.i_instr = block->base;
    state.i_ip = 0;
    j_compile(&state);
    assert(!state.branch_forwards);
    cs_shrink(block, state.i_ip);

    //printf("disas %p %p\n", state.i_instr, state.i_instr + state.i_ip);
    code->jit = (Value (*)(Value*))state.i_instr;
    //printf("alloc    %p\n", code);
}


void code_finalize(Code code) {
    //printf("finalize %p\n", code);
    cs_free(code->jit);
}

#endif /* NJIT */


Code code(index args, index frame, index closed,
          const instr_word* instr, Value* literals) {
    Code code = alloc_code(sizeof *code, 0);
    code->args = args;
    code->frame = frame;
    code->closed = closed;
    code->instr = instr;
    code->literals = literals;

#ifndef NJIT
    jit(code);
#endif

    return code;
}


#ifdef NJIT

#if defined(NDEBUG) && !defined(NVALGRIND)
#define NVALGRIND
#endif

Value run(Value* frame) {
    assert(frame[0]->type == type_func);
    const Func *const this = &frame[0]->func;
    const instr_word *const instr = this->code->instr;

    // note: clearing the stack could even be useful generally, to avoid stale
    //       references in the root set, but is not strictly necessary
#ifndef NVALGRIND
    bzero(frame + (1+this->code->args),
          sizeof *frame * (this->code->frame - (1+this->code->args)));
#endif

    struct value_func closure;
    if (this->code->closed) {
        closure.type_func = type_func;
        closure.vector_func = 0;
        closure.func.code = NULL;
        closure.func.upvalues = alloc(sizeof(Value) * this->code->closed,
                                      alloc_modifyable);
        frame[1+this->code->args] = (Value)&closure;
    }

    Value *const reg[4] = {
        frame,
        closure.func.upvalues,
        this->upvalues,
        this->code->literals
    };

    hold_array(this->code->frame, frame);

    // note: since closure is on the stack, it will not get scanned by the
    // collector even though it's in the frame, so upvalues needs to be
    // added to the root set explicitly (after we return the closure will have
    // been copied somewhere if it persists)
    hold_array(this->code->closed, reg[1]);

    #define REG(x) reg[(x)/INSTR_PART][(x)%INSTR_PART]

    #define INSTR_IP1(bits) uint_fast##bits##_t
    #define INSTR_IP(bits) INSTR_IP1(bits)

    for (INSTR_IP(INSTR_BITS) ip = 0;;) {
        switch (instr[ip] / INSTR_PART) {
        case 0: {
            unsigned verb = instr[ip];
            assert(verb < sizeof verbs_run / sizeof *verbs_run);
            REG(instr[ip+1]) = verbs_run[verb].binary(REG(instr[ip+2]),
                                                      REG(instr[ip+3]));
            ip += 4;
            break;
        }
        case 1: {
            unsigned verb = instr[ip] % INSTR_PART;
            assert(verb < sizeof verbs_run / sizeof *verbs_run);
            REG(instr[ip+1]) = verbs_run[verb].unary(REG(instr[ip+2]));
            ip += 3;
            break;
        }
        case 2: {
            index n = instr[ip] % (INSTR_PART/2) + 2;
            bool partial = instr[ip] % INSTR_PART / (INSTR_PART/2);
            Value f = REG(instr[ip+2]);
            if (n == 2 && !partial)
                REG(instr[ip+1]) =
                    call_binary(f, REG(instr[ip+3]), REG(instr[ip+4]));
            else if (f->type == type_func && n == f->func.code->args &&
                     !partial) {
                Value frame[f->func.code->frame];
                frame[0] = f;
                for (index i = 0; i < n; i++)
                    frame[1+i] = REG(instr[ip+3+i]);
                REG(instr[ip+1]) = run(frame);
            } else {
                Value args[n];
                for (index i = 0; i < n; i++)
                    args[i] = REG(instr[ip+3+i]);
                REG(instr[ip+1]) = partial ? project(f, n, args)
                                           :    call(f, n, args);
            }
            ip += 3 + n;
            break;
        }
        default:
            switch (instr[ip] % INSTR_PART) {
            case 0:
                release_array(2);
                return REG(instr[ip+1]); // fixme: collect before return?
            case 1:
                ip = instr[ip+1];
                continue; // collection unneeded after jumps
            case 2:
                ip = as_condition(REG(instr[ip+2])) ? ip + 3 : instr[ip+1];
                continue; // collection unneeded after jumps
            case 3:
                assert(instr[ip+2] < INSTR_PART &&
                      !frame[instr[ip+2]]->vector &&
                       frame[instr[ip+2]]->type == type_index);
                ip = ((MValue)frame[instr[ip+2]])->index-- > 0 ? instr[ip+1]
                                                               : ip + 3;
                break;
            default:
                assert_failed("unknown instruction");
            }
        }
        COLLECT();
    }
}

#endif /* NJIT */
