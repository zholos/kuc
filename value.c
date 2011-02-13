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

#include "value.h"

#include "adverb.h"
#include "alloc.h"
#include "code.h"
#include "error.h"
#include "func.h"
#include "verb.h"

#include <assert.h>
#include <limits.h>
#include <math.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define index index_hide /* index() should be in string.h anyway */
#include <string.h>
#undef index


//
// Run-time type characteristics
//

#define SIZES(vtype, prefix, name)                \
    sizeof(vtype),                                \
    (short)offsetof(struct value, prefix##name) - \
    (short)offsetof(struct value, item),          \
    sizeof(struct value_##name)

// fixme: move compare functions to types_conv
const struct type types[] = {
  { sizeof(Value*), 0, 0,         0, 1 },
  { SIZES(bool_type,  _, bool),   1, 1 },
  { SIZES(byte_type,  _, byte),   1, 1 },
  { SIZES(int,        _, int),    1, 1 },
  { SIZES(long_type,  _, long),   1, 1 },
  { SIZES(float_type, _, float),  1, 1 },
  { SIZES(char,       _, char),   1, 1 },
  { SIZES(name,       _, name),   1, 1 },
  { SIZES(Map,,          map),    0, 0 },
  { SIZES(Func,,         func),   0, 0 },
  { SIZES(Proj,,         proj),   0, 0 },
  { SIZES(Comp,,         comp),   0, 0 },
  { SIZES(Verb,,         verb),   1, 0 },
  { SIZES(Verb,,         verb),   1, 0 },
  { SIZES(Clause,,       clause), 0, 0 }
};


//
// Type comparisons
//

static int compare_variant_items(const char* x, const char* y) {
    return compare(*(Value*)x, *(Value*)y);
}


#define COMPARE_SCALAR(vtype)                                                \
static int compare_##vtype##_items(const char* x_char, const char* y_char) { \
    vtype##_type x = *(const vtype##_type*)x_char,                           \
                 y = *(const vtype##_type*)y_char;                           \
    return compare_##vtype(x, y);                                            \
}

COMPARE_SCALAR(bool)
COMPARE_SCALAR(byte)
COMPARE_SCALAR(int)
COMPARE_SCALAR(long)
COMPARE_SCALAR(float)
COMPARE_SCALAR(char)
COMPARE_SCALAR(name)


static int compare_map_items(const char* x_char, const char* y_char) {
    Map* x_map = (Map*)x_char;
    Map* y_map = (Map*)y_char;
    int c = compare(x_map->key, y_map->key);
    if (!c)
        return c;
    return compare(x_map->value, y_map->value);
}


static int compare_list(int c, const Value* x, const Value* y, index n) {
    for (index i = 0; i < n; i++) {
        int d = compare(x[i], y[i]);
        if (d == 2 || d == -2)
            return d;
        if (!c)
            c = d;
    }
    return c;
}

#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define MAX(x, y) ((x) > (y) ? (x) : (y))

static int compare_func_items(const char* x_char, const char* y_char) {
    Func* x_func = (Func*)x_char;
    Func* y_func = (Func*)y_char;

    instr_word upvalues = 0, literals = 0;

    const instr_word* instr = x_func->code->instr;
    for (instr_word ip = 0, end = 0; ip <= end;) {
        if (       instr[ip] != y_func->code->instr[ip])
            return instr[ip]  > y_func->code->instr[ip] ? 2 : -2;

        instr_word reg, reg_n;
        switch (instr[ip] / INSTR_PART) {
        case 0:
            reg = ip + 1; reg_n = 3;
            ip += 4;
            end = MAX(end, ip);
            break;
        case 1:
            reg = ip + 1; reg_n = 2;
            ip += 3;
            end = MAX(end, ip);
            break;
        case 2: {
            index n = instr[ip] % (INSTR_PART/2) + 2;
            reg = ip + 1; reg_n = n + 2;
            ip += 3 + n;
            end = MAX(end, ip);
            break;
        }
        default:
            switch (instr[ip] % INSTR_PART) {
            case 0:
                reg = ip+1; reg_n = 1;
                ip += 2;
                break;
            case 1:
                reg_n = 0;
                end = MAX(end, instr[ip+1]);
                ip += 2;
                break;
            case 2:
                reg = ip+2; reg_n = 1;
                end = MAX(end, instr[ip+1]);
                ip += 3;
                end = MAX(end, ip);
                break;
            case 3:
                reg = ip+2; reg_n = 1;
                end = MAX(end, instr[ip+1]);
                ip += 3;
                end = MAX(end, ip);
                break;
            default:
                assert_failed("unknown instruction");
            }
        }

        for (instr_word i = 0; i < reg_n; i++)
            switch (instr[reg+i] / INSTR_PART) {
            case 1:
                upvalues = MAX(upvalues, instr[reg+i] % INSTR_PART + 1);
                break;
            case 3:
                literals = MAX(literals, instr[reg+i] % INSTR_PART + 1);
                break;
            }
    }

    int c = compare_list(0, x_func->code->literals,
                            y_func->code->literals, literals);
    if (c == 2 || c == -2)
        return c;

    if (x_func->upvalues && y_func->upvalues)
        return compare_list(c, x_func->upvalues, y_func->upvalues, upvalues);
    if (x_func->upvalues)
        return  2;
    if (y_func->upvalues)
        return -2;
    return c;
}


static int compare_proj_items(const char* x_char, const char* y_char) {
    Proj* x_proj = (Proj*)x_char;
    Proj* y_proj = (Proj*)y_char;

    int c = compare(x_proj->func, y_proj->func);
    if (c == 2 || c == -2)
        return c;

    index count = MIN(x_proj->count, y_proj->count);
    c = compare_list(c, x_proj->args, y_proj->args, count);
    if (c == 2 || c == -2)
        return c;

    if (x_proj->count > count)
        return  2;
    if (y_proj->count > count)
        return -2;
    return c;
}


static int compare_comp_items(const char* x_char, const char* y_char) {
    return compare_list(0, &(*(Comp*)x_char)[0], &(*(Comp*)x_char)[1], 2);
}


#define compare_verb_prime_items compare_verb_items

static int compare_verb_items(const char* x_char, const char* y_char) {
    Verb x = *(Verb*)x_char,
         y = *(Verb*)y_char;
    return x > y ? 2 : x < y ? -2 : 0;
}


static int compare_clause_items(const char* x_char, const char* y_char) {
    Clause* x_clause = (Clause*)x_char;
    Clause* y_clause = (Clause*)y_char;
    if (x_clause->adverb > y_clause->adverb)
        return  2;
    if (x_clause->adverb < y_clause->adverb)
        return -2;
    return compare(x_clause->verb, y_clause->verb);
}


//
// Null tests
//

static bool null_test_variant(const char* item) {
    return is_null(*(Value*)item);
}

#define NULL_TEST_ATOMIC(vtype)                          \
static bool null_test_##vtype(const char* item) {        \
    return is_null_##vtype(*(const vtype##_type*)item);  \
}

NULL_TEST_ATOMIC(bool)
NULL_TEST_ATOMIC(byte)
NULL_TEST_ATOMIC(int)
NULL_TEST_ATOMIC(long)
NULL_TEST_ATOMIC(float)
NULL_TEST_ATOMIC(char)
NULL_TEST_ATOMIC(name)

#define null_test_map    null_test_equiv
#define null_test_func   null_test_equiv
#define null_test_proj   null_test_equiv
#define null_test_comp   null_test_equiv
#define null_test_verb   null_test_equiv
#define null_test_clause null_test_equiv

static bool null_test_equiv(const char* x) {
    return 0;
}

static bool null_test_verb_prime(const char* x) {
    return !*(const Verb*)x;
}


//
// Type conversions
//

#define CONVERT_VARIANT(rtype)                             \
static rtype##_type variant_to_##rtype(const char* item) { \
    Value v = *(Value*)item;                               \
    if (v->vector)                                         \
        error(error_type);                                 \
    else                                                   \
        return types_conv[v->type]._##rtype(ITEM(v));      \
}

#define CONVERT_READ(rtype)                                \
static rtype##_type rtype##_to_##rtype(const char* item) { \
    return *(rtype##_type*)item;                           \
}

#define CONVERT_TO(rtype, vtype)                                \
static rtype##_type vtype##_to_##rtype(const char* item) {      \
    vtype##_type v = *(vtype##_type*)item;                      \
    return is_null_##vtype(v) ? rtype##_null : (rtype##_type)v; \
}

#define CONVERT_LIMIT(rtype, vtype)                             \
static rtype##_type vtype##_to_##rtype(const char* item) {      \
    vtype##_type v = *(vtype##_type*)item;                      \
    return is_null_##vtype(v) ? rtype##_null :                  \
           v < rtype##_min    ? rtype##_min  :                  \
           v > rtype##_max    ? rtype##_max  : (rtype##_type)v; \
}

#define CONVERT_TO_BOOL(vtype)                       \
static bool_type vtype##_to_bool(const char* item) { \
    vtype##_type v = *(vtype##_type*)item;           \
    return is_null_##vtype(v) ? bool_null : (bool)v; \
}

// note: catching the exception is not very useful for setting min/max,
// because -0W is not the lower limit of int_type
#define CONVERT_FLOAT(rtype, rt)                                         \
static rtype##_type float_to_##rtype(const char* item) {                 \
    float_type f = *(float_type*)item;                                   \
    return is_null_float(f) ? rtype##_null :                             \
           f <= rtype##_min ? rtype##_min  :                             \
           f >= rtype##_max ? rtype##_max  : (rtype##_type)rt##round(f); \
}

#define CONVERT_ERROR(rtype)                             \
static rtype##_type error_to_##rtype(const char* item) { \
    error(error_type);                                   \
}

CONVERT_VARIANT(bool)
CONVERT_READ   (bool)
CONVERT_TO_BOOL(byte)
CONVERT_TO_BOOL(int)
CONVERT_TO_BOOL(long)
CONVERT_TO_BOOL(float)
CONVERT_ERROR  (bool)

CONVERT_VARIANT(byte)
CONVERT_TO     (byte, bool)
CONVERT_READ   (byte)
CONVERT_TO     (byte, int)
CONVERT_TO     (byte, long)
CONVERT_TO     (byte, float)
CONVERT_ERROR  (byte)

CONVERT_VARIANT(int)
CONVERT_TO     (int, bool)
CONVERT_TO     (int, byte)
CONVERT_READ   (int)
CONVERT_LIMIT  (int, long)
CONVERT_FLOAT  (int, l)
CONVERT_ERROR  (int)

CONVERT_VARIANT(long)
CONVERT_TO     (long, bool)
CONVERT_TO     (long, byte)
CONVERT_TO     (long, int)
CONVERT_READ   (long)
CONVERT_FLOAT  (long, ll)
CONVERT_ERROR  (long)

CONVERT_VARIANT(float)
CONVERT_TO     (float, bool)
CONVERT_TO     (float, byte)
CONVERT_TO     (float, int)
CONVERT_TO     (float, long)
CONVERT_READ   (float)
CONVERT_ERROR  (float)


#define COMPARE(vtype) null_test_##vtype, compare_##vtype##_items

#define CONVERT(vtype) vtype##_to_bool, vtype##_to_byte, \
       vtype##_to_int, vtype##_to_long, vtype##_to_float


const char null_name[] = "";

const struct type_conv types_conv[] = {
    { {                      }, COMPARE(variant),    CONVERT(variant) },
    { { ._bool  = bool_null  }, COMPARE(bool),       CONVERT(bool)    },
    { { ._char  = 0          }, COMPARE(byte),       CONVERT(byte)    },
    { { ._int   = int_null   }, COMPARE(int),        CONVERT(int)     },
    { { ._long  = long_null  }, COMPARE(long),       CONVERT(long)    },
    { { ._float = float_null }, COMPARE(float),      CONVERT(float)   },
    { { ._char  = ' '        }, COMPARE(char),       CONVERT(error)   },
    { { ._name  = null_name  }, COMPARE(name),       CONVERT(error)   },
    { {                      }, COMPARE(map),        CONVERT(error)   },
    { {                      }, COMPARE(func),       CONVERT(error)   },
    { {                      }, COMPARE(proj),       CONVERT(error)   },
    { {                      }, COMPARE(comp),       CONVERT(error)   },
    { { ._char = 0           }, COMPARE(verb_prime), CONVERT(error)   },
    { { ._char = 0           }, COMPARE(verb),       CONVERT(error)   },
    { {                      }, COMPARE(clause),     CONVERT(error)   }
};


//
// Value constructors
//

void assert_failed(const char* format, ...) {
    va_list va;
    va_start(va, format);
    fprintf(stderr, "assert failed: ");
    vfprintf(stderr, format, va);
    fputc('\n', stderr);
    exit(EXIT_FAILURE);
}


MValue create_item(Type type) {
    assert(type > type_variant && type < sizeof types / sizeof *types);
    size_t size = types[type].scalar_size;
    MValue value = alloc(size, types[type].atomic + 1);
    value->type = type;
    value->vector = 0;
    return value;
}


static MValue create_item_copy(Type type, const char* item) {
    MValue value = create_item(type);
    COPY(value->item + types[type].offset, item, types[type].size);
    return value;
}


MValue create_items(Type type, index count) {
    assert(type >= type_variant && type < sizeof types / sizeof *types);
    assert(types[type].vectorable);
    size_t size = offsetof(struct value, items[0]) + types[type].size * count;
    MValue value = alloc(size, types[type].atomic + 1);
    value->type = type;
    value->vector = 1;
    value->count = count;
    return value;
}


const struct value_bool bool_literals[3] = {
    { type_bool, 0, -1 },
    { type_bool, 0,  0 },
    { type_bool, 0,  1 }
};

Value create_bool(bool_type b) {
    assert(b >= -1 && b <= 1);
    return (Value)&bool_literals[b + 1];
}


Value create_byte(byte_type b) {
    MValue value = create_item(type_byte);
    value->_byte = b;
    return value;
}


Value create_char(char c) {
    MValue value = create_item(type_char);
    value->_char = c;
    return value;
}


#define SMALL_INTS_MIN 0
#define SMALL_INTS_MAX 32
static struct value_int small_ints[SMALL_INTS_MAX - SMALL_INTS_MIN];

static void __attribute__ ((constructor)) small_ints_init() {
    for (int i = 0; i < sizeof small_ints / sizeof *small_ints; i++) {
        small_ints[i].type_int = type_int;
        small_ints[i].vector_int = 0;
        small_ints[i]._int = SMALL_INTS_MIN + i;
    }
}

Value create_int(int i) {
    if (i >= SMALL_INTS_MIN && i < SMALL_INTS_MAX)
        return (Value)&small_ints[i - SMALL_INTS_MIN];
    else {
#ifndef NSHORTCUT
        MValue value = alloc(sizeof(struct value_int), alloc_atomic);
        value->type = type_int;
        value->vector = 0;
        value->_int = i;
        return value;
#else
        MValue value = create_item(type_int);
        value->_int = i;
        return value;
#endif
    }
}


Value create_long(long_type i) {
    MValue value = create_item(type_long);
    value->_long = i;
    return value;
}


Value create_float(float_type f) {
    MValue value = create_item(type_float);
    value->_float = f;
    return value;
}


static Value create_name_base(name n) {
    MValue value = create_item(type_name);
    value->_name = n;
    return value;
}


MValue create_string(const char* s, size_t n) {
    if (n >= index_max)
        error(error_length);
    MValue value = create_items(type_char, n);
    memcpy(value->items, s, n);
    return value;
}


MValue create_stringz(const char* s) {
    return create_string(s, strlen(s));
}


Value create_map(Value key, Value value) {
    if (!key->vector || !value->vector || key->count != value->count)
        assert_failed("create map from incompatible values");
    MValue r = create_item(type_map);
    r->map.key = key;
    r->map.value = value;
    return r;
}


const struct value_verb untyped_null = { type_verb_prime, 0, verb_null };
const struct value_mixed empty = { type_variant, 1, 0 };


MValue box(Value x) {
    MValue r = create_items(type_variant, 1);
    r->mixed[0] = x;
    return r;
}


MValue cons(Value x, Value y) {
    MValue r = create_items(type_variant, 2);
    r->mixed[0] = x;
    r->mixed[1] = y;
    return r;
}


MValue triplet(Value x, Value y, Value z) {
    MValue r = create_items(type_variant, 3);
    r->mixed[0] = x;
    r->mixed[1] = y;
    r->mixed[2] = z;
    return r;
}


Value unlist(Value x) {
    index count = 0;
    for (Value i = x; i->count; i = i->mixed[0])
        count = add_length(count, 1);

    MValue r = create_items(type_variant, count);
    for (Value i = x; i->count; i = i->mixed[0]) {
        assert(i->count == 2);
        r->mixed[--count] = i->mixed[1];
    }
    return r;
}


//
// List copying
//

MValue copy(Value x) {
    if (x->vector) {
        MValue r = create_items(x->type, x->count);
        COPIES(r->items, x->items, types[x->type].size, x->count);
        return r;
    } else
        return create_item_copy(x->type, ITEM(x));
}


MValue replicate(Value x, index n) {
    assert(n >= 0);
    if (x->vector || !types[x->type].atomic) {
        MValue r = create_items(type_variant, n);
        for (index i = 0; i < n; i++)
            r->mixed[i] = x;
        return r;
    } else {
        size_t size = types[x->type].size;
        const char* item = x->item + types[x->type].offset;
        MValue r = create_items(x->type, n);
        for (index i = 0; i < n; i++)
            COPY(r->items + size * i, item, size);
        return r;
    }
}


MValue subvector(Value x, index pos, index len) {
    assert(x->vector && pos >= 0 && add_length(pos, len) <= x->count);
    size_t size = types[x->type].size;
    MValue r = create_items(x->type, len);
    COPIES(r->items, x->items + size * pos, size, len);
    return r;
}


Value null_equivalent(Value x) {
    if (IS_MIXED(x)) {
        MValue r = create_items(type_variant, x->count);
        for (index i = 0; i < x->count; i++)
            r->mixed[i] = null_equivalent(x->mixed[i]);
        return r;
    } else if (types[x->type].atomic) {
        const char* null = (const char*)&types_conv[x->type].null;
        MValue r;
        if (x->vector) {
            size_t size = types[x->type].size;
            r = create_items(x->type, x->count);
            for (index i = 0; i < x->count; i++)
                COPY(r->items + size * i, null, size);
        } else
            r = create_item_copy(x->type, null);
        return r;
    } else
        return (Value)&untyped_null;
}


Value item(Value x, index i) {
    // note: assumes x is vector and i is valid
    assert(x->vector && i >= 0 && i < x->count);
    if (x->type == type_variant) // automatically strengthen
        return x->mixed[i];
    else
        return create_item_copy(x->type, x->items + types[x->type].size * i);
}


Value item_null(Value x, index i) {
    // note: assumes x is vector
    assert(x->vector);
    if (i < 0 || i >= x->count) {
        if (IS_MIXED(x))
            return !x->count ? (Value)&empty : null_equivalent(x->mixed[0]);
        else {
            assert(types[x->type].atomic);
            const char* null = (const char*)&types_conv[x->type].null;
            return create_item_copy(x->type, null);
        }
    }
    return item(x, i);
}


Value strengthen(Value x) {
    // note: assumes x is mixed vector
    assert(IS_MIXED(x));
    index n = x->count;
    if (n == 0)
        return (Value)&empty;

    Type type = x->mixed[0]->type;
    if (x->mixed[0]->vector || !types[type].vectorable)
        return x;
    for (index i = 1; i < n; i++)
        if (x->mixed[i]->vector || x->mixed[i]->type != type)
            return x;

    size_t size = types[type].size;
    short offset = types[type].offset;
    MValue r = create_items(type, n);
    for (index i = 0; i < n; i++)
        COPY(r->items + size * i, x->mixed[i]->item + offset, size);
    return r;
}


MValue weaken(Value x) {
    // note: assumes x is vector but not mixed
    assert(x->vector && x->type != type_variant);
    return weaken_to(x, x->count);
}


MValue weaken_to(Value x, index i) {
    // note: assumes x is vector but not mixed and i is in range
    assert(x->vector && x->type != type_variant && i >= 0 && i <= x->count);
    MValue r = create_items(type_variant, x->count);
    for (index j = 0; j < i; j++)
        r->mixed[j] = item(x, j);
    return r;
}


//
// Comparisons and conversions
//

bool is_null(Value x) {
    return x->vector ? 0 : types_conv[x->type].is_null(ITEM(x));
}


static int compare_numeric(Value x, Value y) {
    assert(IS_NUMERIC(x) && IS_NUMERIC(y));
    assert(x->vector == y->vector && x->type > y->type);

    switch (x->type) {
#define COMPARE_CLAUSE(vtype)                                               \
    case type_##vtype: {                                                    \
        vtype##_type (*conv)(const char*) = types_conv[y->type]._##vtype;   \
        size_t size = types[y->type].size;                                  \
        if (x->vector) {                                                    \
            index count = MIN(x->count, y->count);                          \
            for (index i = 0; i < count; i++) {                             \
                vtype##_type y_##vtype = conv(y->items + size * i);         \
                int c = compare_##vtype(x->vtype##s[i], y_##vtype);         \
                if (c)                                                      \
                    return c;                                               \
            }                                                               \
            if (x->count > count)                                           \
                return  2;                                                  \
            if (y->count > count)                                           \
                return -2;                                                  \
        } else {                                                            \
            vtype##_type y_##vtype = conv(y->item + types[y->type].offset); \
            int c = compare_##vtype(x->_##vtype, y_##vtype);                \
            if (c)                                                          \
                return c;                                                   \
        }                                                                   \
        break;                                                              \
    }
    // note: bool is smallest numeric type, so clause not needed
    COMPARE_CLAUSE(byte)
    COMPARE_CLAUSE(int)
    COMPARE_CLAUSE(long)
    COMPARE_CLAUSE(float)
    default:
        assert_failed("comparison for numeric type not implemented");
    }
    return 1;
}


int compare(Value x, Value y) {
    if (x == y) // shortcut and for NULLs
        return  0;
    if (!y)
        return  2;
    if (!x)
        return -2;

    if (x->vector != y->vector)
        return x->vector - y->vector;

    if (x->type != y->type)
        if (IS_NUMERIC(x) && IS_NUMERIC(y))
            if (x->type > y->type)
                return compare_numeric(x, y);
            else
                return -compare_numeric(y, x);
        else
            return x->type > y->type ? 2 : -2;

    int (*compare)(const char*, const char*) = types_conv[x->type].compare;
    if (x->vector) {
        size_t size = types[x->type].size;
        for (index i = 0; i < x->count && i < y->count; i++) {
            int c = compare(x->items + size * i, y->items + size * i);
            if (c)
                return c;
        }
        return x->count > y->count ? 1 : x->count < y->count ? -1 : 0;
    } else {
        short offset = types[x->type].offset;
        return compare(x->item + offset, y->item + offset);
    }
}


index find_item(Value x, Value y) {
    if (!x->vector)
        error(error_type);
    if (x->type == type_variant) {
        for (index i = 0; i < x->count; i++)
            if (!compare(x->mixed[i], y))
                return i;
        return x->count;
    } else {
        Type type = x->type;
        if (y->vector || y->type != type)
            error(error_type);
        int (*compare)(const char*, const char*) = types_conv[type].compare;
        size_t size  = types[type].size;
        short offset = types[type].offset;
        for (index i = 0; i < x->count; i++)
            if (!compare(x->items + size * i, y->item + offset))
                return i;
        return x->count;
    }
}


bool in(Value x, Value y) {
    return find_item(x, y) < x->count;
}


bool as_condition(Value x) {
    if (x->vector)
        error(error_cond);
#ifndef NSHORTCUT
    if (x->type == type_bool)
        return x->_bool > 0;
    if (x->type == type_int)
        return !is_null_int(x->_int) && x->_int;
#endif
    return types_conv[x->type]._bool(ITEM(x)) > 0;
}


bool as_condition_no_shortcut(Value x) {
    if (x->vector)
        error(error_cond);
    return types_conv[x->type]._bool(ITEM(x)) > 0;
}


index as_index(Value x) {
    if (x->vector)
        error(error_type);
#ifndef NSHORTCUT
    if (x->type == type_index)
        return x->index;
#endif
    return types_conv[x->type]._int(ITEM(x)); // note: assumes index is int
}


index item_as_index(Value x, index i) {
    // note: assumes x is vector and i is in range
    assert(x->vector && i >= 0 && i < x->count);
    return types_conv[x->type]._int(x->items + types[x->type].size * i);
           // note: assumes index is int
}


void check_length(index x) {
    if (x < 0 || x >= index_max)
        error(error_length);
}


index add_length(index x, index y) {
    // assumes x is within bounds
    if (y < 0 || y >= index_max - x)
        error(error_length);
    return x + y;
}


//
// List in-place changing
//

void push(MValue* x, Value y) {
    assert((*x)->vector && (!y->vector && (*x)->type == y->type ||
                                          (*x)->type == type_variant));
    index c = add_length((*x)->count, 1);
    size_t size = types[(*x)->type].size;
    *x = resize_alloc(*x, offsetof(struct value, items[0]) + size * c);
    if ((*x)->type == type_variant)
        (*x)->mixed[c-1] = y;
    else
        COPY((*x)->items + size * (c-1), ITEM(y), size);
    (*x)->count = c;
}


void push_index(MValue* x, index y) {
    assert((*x)->vector && (*x)->type == type_index);
    index c = add_length((*x)->count, 1);
    *x = resize_alloc(*x, offsetof(struct value, items[0]) + sizeof y * c);
    (*x)->indexes[c-1] = y;
    (*x)->count = c;
}


void push_weaken(MValue* x, Value y) {
    // x must be a vector, will be weakened if necessary
    assert((*x)->vector);
    if ((*x)->type != type_variant && !(!y->vector && (*x)->type == y->type))
        *x = weaken(*x);
    push(x, y);
}


index insert(MValue* x, Value y) {
    assert((*x)->vector);
    index i = find_item(*x, y);
    if (i == (*x)->count)
        push(x, y);
    return i;
}


void append(MValue* x, Value y) {
    assert((*x)->vector && y->vector && (*x)->type == y->type);
    index n = add_length((*x)->count, y->count);
    size_t size = types[(*x)->type].size;
    *x = resize_alloc(*x, offsetof(struct value, items[0]) + size * n);
    COPIES((*x)->items + size * (*x)->count, y->items, size, y->count);
    (*x)->count = n;
}


void resize(MValue* x, index n) {
    assert((*x)->vector && n >= 0);
#ifndef NSHORTCUT
    if (n == (*x)->count)
        return;
#endif
    size_t size = types[(*x)->type].size;
    *x = resize_alloc(*x, offsetof(struct value, items[0]) + size * n);
    (*x)->count = n;
}


void delete(MValue* x, index i) {
    assert((*x)->vector && i >= 0 && i < (*x)->count);
    size_t size = types[(*x)->type].size;
    COPIES((*x)->items + size * i, (*x)->items + size * (i + 1),
            size, (*x)->count - (i + 1));
    *x = resize_alloc(*x,
                      offsetof(struct value, items[0]) + size * --(*x)->count);
}


void amend(MValue* x, Value y, Value z) {
    // fixme: error conditions should be checked by callers
    if ((*x)->type == type_map) {
        index i = find_item((*x)->map.key, y);
        if (i < (*x)->map.key->count)
            amend_vector((MValue*)&(*x)->map.value, i, z);
        else {
            push((MValue*)&(*x)->map.key,   y);
            push((MValue*)&(*x)->map.value, z);
        }
    } else if ((*x)->vector) {
        if ((*x)->type != type_variant && !types[(*x)->type].atomic)
            error(error_type);
        if (y->vector) {
            if (z->vector && z->count != y->count)
                error(error_length);
            for (index i = 0; i < y->count; i++) {
                index j = item_as_index(y, i);
                if (j < 0 || j >= (*x)->count)
                    error(error_index);
                Value v = z->vector ? item(z, i) : z;
                if ((*x)->type == type_variant)
                    (*x)->mixed[j] = v;
                else if ((*x)->type == v->type && !v->vector) {
                    size_t size = types[v->type].size;
                    COPY((*x)->items + size * j, ITEM(v), size);
                } else
                    error(error_type);
            }
        } else
            amend_vector(x, as_index(y), z);
    } else
        error(error_type);
}


void amend_vector(MValue* x, index i, Value y) {
    if (i < 0 || i >= (*x)->count)
        error(error_index);
    if ((*x)->type == type_variant)
        (*x)->mixed[i] = y;
    else if ((*x)->type == y->type && !y->vector) {
        size_t size = types[y->type].size;
        COPY((*x)->items + size * i, ITEM(y), size);
    } else
        error(error_type);
}


void amend_weaken(MValue* x, index i, Value y) {
    // x must be a vector, will be weakened if necessary;
    // i must be in range
    assert((*x)->vector && i >= 0 && i < (*x)->count);
    if ((*x)->type != type_variant && !(!y->vector && (*x)->type == y->type))
        *x = weaken(*x);
    if ((*x)->type == type_variant)
        (*x)->mixed[i] = y;
    else {
        size_t size = types[(*x)->type].size;
        COPY((*x)->items + size * i, ITEM(y), size);
    }
}


//
// Name table
//

typedef struct name {
    struct name *name_left, *name_right;
    short name_balance;
    char chars[];
}* Name;


#define TREE_PREFIX name
#define TREE_NODE Name
#define TREE_SAME( node, tree) !strcmp((node)->chars, (tree)->chars)
#define TREE_LEFT( node, tree) (strcmp((node)->chars, (tree)->chars) < 0)
#define TREE_RIGHT(node, tree) (strcmp((node)->chars, (tree)->chars) > 0)
#define TREE_INSERT_ONLY
#include "tree.h"

Name name_tree;


static void* malloc_checked(size_t size) {
    void* memory = malloc(size);
    if (!memory)
        memory_error(size);
    return memory;
}


static name find_name(const char* chars, size_t count) {
    if (count > index_max)
        error(error_length);

    if (count == 0)
        return null_name;

    int c;
    for (Name n = name_tree; n;
              n = c <= 0 ? n->name_left : n->name_right) {
        c = strncmp(chars, n->chars, count);
        if (!c && !n->chars[count])
            return n->chars;
    }

    Name n = malloc_checked(sizeof *n + count + 1);
    n->name_left    = NULL;
    n->name_right   = NULL;
    n->name_balance = 0;
    memcpy(n->chars, chars, count);
    n->chars[count] = 0;

    if (!name_tree)
        name_tree = n;
    else
        name_insert_node(&name_tree, n);

    return n->chars;
}


Value create_name(const char* chars, size_t count) {
    return create_name_base(find_name(chars, count));
}


Value create_namez(const char* chars) {
    return create_name_base(find_name(chars, strlen(chars)));
}


Value             name_null,
                  name_x,         name_y,         name_z,
                  error_type,     error_length,   error_index,
                  error_shape,    error_cond,     error_count,
                  error_rank,     error_range,    error_todo,
                  error_file,     error_sys,      error_parse,
                  error_expected, error_unknown,  error_number,
                  error_string,   error_name,     error_compile,
                  error_literals, error_temps,    error_args,
                  error_locals,   error_code;
struct value_name name_user,      name_system,    name_value;
name name_self,   name_if,   name_while, name_do,
     name_bool,   name_byte, name_int,   name_long,
     name_float,  name_char, name_name,  name_verb,
     name_adverb;

static void __attribute__ ((constructor)) names_init() {
    static struct {
        Value* value;
        struct value_name* value_name;
        name* name;
        const char* s;
        struct value_name literal;
    } info[] = {
                         { &name_null,    NULL, NULL, "" },

#define VALUE(name)      { &name_##name,  NULL, NULL, #name }
        VALUE(x),             VALUE(y),             VALUE(z),

#define VALUE_NAME(name) { NULL, &name_##name, NULL, #name }
        VALUE_NAME(user),     VALUE_NAME(system),   VALUE_NAME(value),

#define ERROR_NAME(name) { &error_##name, NULL, NULL, #name }
        ERROR_NAME(type),     ERROR_NAME(length),   ERROR_NAME(index),
        ERROR_NAME(shape),    ERROR_NAME(cond),     ERROR_NAME(count),
        ERROR_NAME(rank),     ERROR_NAME(range),    ERROR_NAME(todo),
        ERROR_NAME(file),     ERROR_NAME(sys),      ERROR_NAME(parse),
        ERROR_NAME(expected), ERROR_NAME(unknown),  ERROR_NAME(number),
        ERROR_NAME(string),   ERROR_NAME(name),     ERROR_NAME(compile),
        ERROR_NAME(literals), ERROR_NAME(temps),    ERROR_NAME(args),
        ERROR_NAME(locals),   ERROR_NAME(code),

#define NAME_NAME(name) { NULL, NULL, &name_##name, #name }
        NAME_NAME(self),   NAME_NAME(if),   NAME_NAME(while), NAME_NAME(do),
        NAME_NAME(bool),   NAME_NAME(byte), NAME_NAME(int),   NAME_NAME(long),
        NAME_NAME(float),  NAME_NAME(char), NAME_NAME(name),  NAME_NAME(verb),
        NAME_NAME(adverb)
    };

    for (int i = 0; i < sizeof info / sizeof *info; i++) {
        name n = find_name(info[i].s, strlen(info[i].s));
        if (info[i].value) {
            info[i].literal.type_name = type_name;
            info[i].literal.vector_name = 0;
            info[i].literal._name = n;
           *info[i].value = (Value)&info[i].literal;
        }
        if (info[i].value_name) {
            info[i].value_name->type_name = type_name;
            info[i].value_name->vector_name = 0;
            info[i].value_name->_name = n;
        }
        if (info[i].name)
           *info[i].name = n;
    }
}
