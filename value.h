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

#ifndef VALUE_H
#define VALUE_H

#include <stddef.h> /* for size_t */

//#include <stdbool.h>
typedef _Bool bool; // typedef bool instead because we use the symbol in macros
                    // in a different meaning


// type definitions
struct value;
typedef const struct value*  Value;
typedef       struct value* MValue;

typedef const char* name;
typedef short Type;
typedef int index;
#define INDEX_SUFFIX(name) name##_int

typedef Value         variant_type;
typedef signed char   bool_type;
typedef unsigned char byte_type;
typedef int           int_type;
typedef long long     long_type;
typedef double        float_type;
typedef char          char_type;
typedef name          name_type;

typedef struct Map {
    Value key;   // vector
    Value value; // vector
} Map;

typedef struct func {
    struct code* code;
    Value* upvalues;
} Func;

typedef struct proj {
    Value func;
    index count;
    Value* args; // guarantted to have at least one non-null element
} Proj;

typedef Value Comp[2];

typedef unsigned char Verb;
typedef unsigned char Adverb;

typedef struct clause {
    Adverb adverb;
    Value verb;
} Clause;


#define VALUE_ITEM(vtype, prefix, name)            \
    struct value_##name {                          \
        Type type_##name;                          \
        bool vector_##name;                        \
        vtype prefix##name;                        \
    };

#define VALUE_ITEMS(vtype, prefix, suffix, name)           \
    VALUE_ITEM(vtype, prefix, name)                        \
    struct value_##name##suffix##s {                       \
        Type type_##name##suffix##s;                       \
        bool vector_##name##suffix##s;                     \
        index count_##name##suffix##s;                     \
        vtype name##suffix##s[] __attribute__ ((aligned)); \
    };

// note: initial elements of structures must all match (6.5.2.3/5)
struct value {
    union {
        struct value_vector {
            Type type;
            bool vector;
            index count;
            char items[] __attribute__ ((aligned));
        };
        struct value_scalar {
            Type type_item;
            bool vector_item;
            char item[];
        };
        struct value_mixed {
            Type type_mixed;
            bool vector_mixed;
            index count_mixed;
            Value mixed[] __attribute__ ((aligned));
        };
        VALUE_ITEMS(bool_type,  _,, bool)
        VALUE_ITEMS(byte_type,  _,, byte)
        VALUE_ITEMS(int,        _,, int)
        VALUE_ITEMS(int,,        e, index)
        VALUE_ITEMS(long_type,  _,, long)
        VALUE_ITEMS(float_type, _,, float)
        VALUE_ITEMS(char,       _,, char)
        VALUE_ITEMS(name,       _,, name)
        VALUE_ITEM(Map,,    map)
        VALUE_ITEM(Func,,   func)
        VALUE_ITEM(Proj,,   proj)
        VALUE_ITEM(Comp,,   comp)
        VALUE_ITEM(Verb,,   verb)
        VALUE_ITEM(Clause,, clause)
    };
};

#undef VALUE_ITEMS
#undef VALUE_ITEM

#define ITEM(x) ((x)->item + types[(x)->type].offset)

// there are no variant scalars, so don't need to test for vector
#define IS_MIXED(value) ((value)->type == type_variant)

#define IS_NULL(value) ((value)->type == type_verb_prime && \
                        (value)->verb == verb_null)
#define IS_NUMERIC(value) ((value)->type >= type_numeric_first && \
                           (value)->type <= type_numeric_last)
#define IS_INTEGER(value) ((value)->type >= type_integer_first && \
                           (value)->type <= type_integer_last)
#define IS_CALLABLE(value) ((value)->type >= type_callable_first && \
                            (value)->type <= type_callable_last)


enum {
    type_variant,
    type_bool,
        type_numeric_first = type_bool,
        type_integer_first = type_bool,
    type_byte,
    type_int,
        type_index = type_int,
    type_long,
        type_integer_last = type_long,
    type_float,
        type_numeric_last = type_float,
    type_char,
    type_name,
    type_map,
    type_func,
        type_callable_first = type_func,
    type_proj,
    type_comp,
    type_verb_prime,
    type_verb,
    type_clause,
        type_callable_last = type_clause
};


// compile-time type characteristics
// fixme: temporary for byte
#define bool_null  -1
#define byte_null  0
#define int_null   INT_MIN
#define long_null  LONG_MIN
#define float_null NAN
#define char_null  ' '

// fixme: temporary for bool and byte
#define bool_min  0
#define byte_min  0
#define int_min   (INT_MIN+1)
#define long_min  (INT_MIN+1)
#define float_min (-(float_type)INFINITY)

#define bool_max  1
#define byte_max  UCHAR_MAX
#define int_max   INT_MAX
#define index_max int_max
#define long_max  LONG_MAX
#define float_max ((float_type)INFINITY)

#define is_null_bool(x)  ((x) < 0)
#define is_null_byte(x)  0
#define is_null_int(x)   ((x) == int_null)
#define is_null_long(x)  ((x) == long_null)
#define is_null_float(x) isnan(x)
#define is_null_char(x)  ((x) == char_null)
#define is_null_name(x)  (!*(x))

#define compare_bool(x, y) ((x) > (y) ? 2 : (x) < (y) ? -2 : 0)
#define compare_byte compare_bool
#define compare_int  compare_bool
#define compare_long compare_bool
#define compare_char compare_bool
#define compare_float(x, y) \
    (isnan(x) ? isnan(y) ? 0 : -2 : isnan(y) ? 2 : compare_bool((x), (y)))
#define compare_name(x, y) \
    (strcmp((x), (y)) > 0 ? 2 : strcmp((x), (y)) < 0 ? -2 : 0)


// run-time type characteristics
extern const struct type {
    size_t size; // size of item
    short offset;
    short scalar_size; // size of scalar structure (header and item)
    bool atomic;
    bool vectorable; // variant is the only vectorable non-atomic type
} types[15];

// more type characteristics
extern const struct type_conv {
    union {
        char       _char;
        bool_type  _bool;
        int        _int;
        long_type  _long;
        float_type _float;
        name       _name;
    } null;
    bool       (*is_null)(const char*);
    int        (*compare)(const char*, const char*);
    bool_type  (*_bool)  (const char*);
    byte_type  (*_byte)  (const char*);
    int        (*_int)   (const char*);
    long_type  (*_long)  (const char*);
    float_type (*_float) (const char*);
} types_conv[15];


void assert_failed(const char* format, ...) __attribute__ ((noreturn, cold));

MValue create_item(Type type)               __attribute__ ((hot));
MValue create_items(Type type, index count) __attribute__ ((hot));

Value create_bool(bool_type)   __attribute__ ((hot));
Value create_byte(byte_type)   __attribute__ ((hot));
Value create_char(char)        __attribute__ ((hot));
Value create_int(int)          __attribute__ ((hot));
#define create_index(x) (INDEX_SUFFIX(create)(x))
Value create_long(long_type)   __attribute__ ((hot));
Value create_float(float_type) __attribute__ ((hot));
MValue create_string(const char*, size_t);
MValue create_stringz(const char*);
Value create_name(const char*, size_t);
Value create_namez(const char*);
Value create_map(Value, Value);

extern const struct value_verb untyped_null;
extern const struct value_mixed empty;

#define COPY(to, from, size) memcpy(to, from, size)
#define COPIES(to, from, size, count) memcpy(to, from, (size_t)(size) * (count))

MValue box(Value);
MValue cons(Value, Value);
MValue triplet(Value, Value, Value);
Value unlist(Value);

MValue copy(Value)             __attribute__ ((hot));
MValue replicate(Value, index);
MValue subvector(Value, index pos, index len);
Value null_equivalent(Value);
Value item(Value, index)       __attribute__ ((hot));
Value item_null(Value, index)  __attribute__ ((hot));
Value strengthen(Value)        __attribute__ ((hot));
MValue weaken(Value)           __attribute__ ((hot));
MValue weaken_to(Value, index) __attribute__ ((hot));

bool is_null(Value);
int compare(Value, Value); // lexicographical, not numerical
index find_item(Value, Value);
bool in(Value, Value);
bool as_condition(Value);
bool as_condition_no_shortcut(Value);
index as_index(Value);
index item_as_index(Value, index);

void check_length(index);
index add_length(index, index);

void push(MValue*, Value);
void push_index(MValue*, index);
void push_weaken(MValue*, Value);
index insert(MValue*, Value);
void append(MValue*, Value);
void resize(MValue*, index);
void delete(MValue*, index);
void amend(MValue*, Value, Value);
void amend_vector(MValue*, index, Value);
void amend_weaken(MValue*, index, Value);


extern Value             name_null,
                         name_x,         name_y,         name_z,
                         error_type,     error_length,   error_index,
                         error_shape,    error_cond,     error_count,
                         error_rank,     error_range,    error_todo,
                         error_file,     error_sys,      error_parse,
                         error_expected, error_unknown,  error_number,
                         error_string,   error_name,     error_compile,
                         error_literals, error_temps,    error_args,
                         error_locals,   error_code;
extern struct value_name name_user, name_system, name_value;
extern name name_self,   name_if,   name_while, name_do,
            name_bool,   name_byte, name_int,   name_long,
            name_float,  name_char, name_name,  name_verb,
            name_adverb;

            

#endif /* VALUE_H */
