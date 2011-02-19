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

#include "arith.h"

#include "error.h"
#include "verb.h"

#include <assert.h>
#include <limits.h>
#include <math.h>

#define index index_hide /* index() should be in string.h anyway */
#include <string.h>
#undef index


#ifndef NSHORTCUT
#define SHORTCUT(x) x
#else
#define SHORTCUT(x)
#endif


static Value map_binary(Value (*f)(Value, Value), Value (*only_right)(Value),
                        Value x, Value y) {
    assert(x->type == type_map && y->type == type_map);

    // using a vector operation when keys are identical would be a special case,
    // not a shortcut, because keys might not be unique

    // todo: check that this doesn't reach c.
    bool copied_key = 0;
    MValue r_key = (MValue)x->map.key;
    MValue r_value = copy(x->map.value);
    for (index i = 0; i < y->map.key->count; i++) {
        Value v = item(y->map.value, i);
        Value k = item(y->map.key,   i);
        index j = find_item(r_key, k);
        if (j < r_key->count)
            amend_weaken(&r_value, j, f(item(r_value, j), v));
        else {
            if (!copied_key) {
                r_key = copy(r_key);
                copied_key = 1;
            }
            push_weaken(&r_key, k);
            push_weaken(&r_value, only_right(v));
        }
    }
    return create_map(r_key, IS_MIXED(r_value) ? strengthen(r_value) : r_value);
}


/* binary verbs are parametrized by:
   name    - the name of the verb and, correspondingly, of the primitive
             functions
   rhs     - the function applied to values in right map when no value matches
             in left map
   clauses - which type clauses are present and what their results are
*/
#define BINARY(name, rhs, clauses)                                        \
Value name(Value x, Value y) {                                            \
    if (x->vector) {                                                      \
        index n = x->count;                                               \
        if (y->vector) {                                                  \
            if (n != y->count)                                            \
                error(error_length);                                      \
            if (x->type == type_variant || y->type == type_variant) {     \
                MValue r = create_items(type_variant, n);                 \
                for (index i = 0; i < n; i++)                             \
                    r->mixed[i] = name(item(x, i), item(y, i));           \
                return strengthen(r);                                     \
            }                                                             \
            clauses(CLAUSE_VV, name)                                      \
        } else {                                                          \
            if (x->type == type_variant) {                                \
                MValue r = create_items(type_variant, n);                 \
                for (index i = 0; i < n; i++)                             \
                    r->mixed[i] = name(x->mixed[i], y);                   \
                return strengthen(r);                                     \
            }                                                             \
            clauses(CLAUSE_VA, name)                                      \
            if (y->type == type_map)                                      \
                goto map_y;                                               \
            }                                                             \
    } else                                                                \
        if (y->vector) {                                                  \
            index n = y->count;                                           \
            if (y->type == type_variant) {                                \
                MValue r = create_items(type_variant, n);                 \
                for (index i = 0; i < n; i++)                             \
                    r->mixed[i] = name(x, y->mixed[i]);                   \
                return strengthen(r);                                     \
            }                                                             \
            clauses(CLAUSE_AV, name)                                      \
            if (x->type == type_map)                                      \
                goto map_x;                                               \
        } else {                                                          \
            clauses(CLAUSE_AA, name)                                      \
            if (x->type == type_map)                                      \
                if (y->type == type_map)                                  \
                    return map_binary(name, rhs, x, y);                   \
                else map_x:                                               \
                    return create_map(x->map.key, name(x->map.value, y)); \
            else if (y->type == type_map) map_y:                          \
                return create_map(y->map.key, name(x, y->map.value));     \
        }                                                                 \
    error(error_type);                                                    \
}

#define SCALAR_BINARY(name, clauses)           \
Value scalar_##name(Value x, Value y) {        \
    assert(!x->vector && x->type != type_map); \
    assert(!y->vector && y->type != type_map); \
    clauses(CLAUSE_AA, name)                   \
    error(error_type);                         \
}

/* value types for parametrizing clauses:
   TAKE    - expect the named type precisely and use the data members directly
   CONV    - expect the named type or any preceding type and use the appropriate
             conversion function to get a value of the named type
   VARIANT - expect a variant vector and use item() to get values
*/

#define TAKE(type) (type,    ==, _##type, TAKE_ITEM, TAKE_ITEMS)
#define CONV(type) (type,    <=, _##type, CONV_ITEM, CONV_ITEMS)

#define TAKE_ITEM(    rtype, v) (v->_##rtype)
#define TAKE_ITEMS(   rtype, v) (v->rtype##s[i])
#define CONV_ITEM(    rtype, v) types_conv[v->type]._##rtype(v->item + \
                                     types[v->type].offset)
#define CONV_ITEMS(   rtype, v) types_conv[v->type]._##rtype(v->items + \
                                     types[v->type].size * i)

#define PASTE1(x, y) x##y
#define PASTE(x, y) PASTE1(x, y)

#define TYPE_TYPE(type, c, s, i, is) type
#define TYPE_NAME(type, c, s, i, is) type_##type
#define TYPE_CTYPE(type, c, s, i, is) type##_type
#define TYPE_COMP(t, comp, s, i, is) comp

#define TYPE_FUNC1(t, c, suffix, i, is) suffix
#define TYPE_FUNC(type, name) PASTE(name, TYPE_FUNC1 type)

#define TYPE_ITEM1(t, c, s, item, is)  item
#define TYPE_ITEM2(take, rtype, v) take(rtype, v)
#define TYPE_ITEM(type, v)  TYPE_ITEM2(TYPE_ITEM1  type, TYPE_TYPE type, v)

#define TYPE_ITEMS1(t, c, s, i, items) items
#define TYPE_ITEMS(type, v) TYPE_ITEM2(TYPE_ITEMS1 type, TYPE_TYPE type, v)

#define IF_TYPE_B(vtype)                               \
    if ((x->type  TYPE_COMP vtype  TYPE_NAME vtype) && \
        (y->type  TYPE_COMP vtype  TYPE_NAME vtype))


/* clauses are parametrized by:
   name   - the primitive function
   rtype  - the result type name
   vtype  - the value type object (TAKE, CONV or VARIANT)
*/
#define CLAUSE_VV(name, rtype, vtype)                         \
    IF_TYPE_B(vtype) {                                        \
        MValue r = create_items(type_##rtype, n);             \
        for (index i = 0; i < n; i++)                         \
            r->rtype##s[i] =                                  \
                TYPE_FUNC(vtype, name)(TYPE_ITEMS(vtype, x),  \
                                       TYPE_ITEMS(vtype, y)); \
        return r;                                             \
    }

#define CLAUSE_VA(name, rtype, vtype)                            \
    IF_TYPE_B(vtype) {                                           \
        TYPE_CTYPE vtype  v = TYPE_ITEM(vtype, y);               \
        MValue r = create_items(type_##rtype, n);                \
        for (index i = 0; i < n; i++)                            \
            r->rtype##s[i] =                                     \
                TYPE_FUNC(vtype, name)(TYPE_ITEMS(vtype, x), v); \
        return r;                                                \
    }

#define CLAUSE_AV(name, rtype, vtype)                            \
    IF_TYPE_B(vtype) {                                           \
        TYPE_CTYPE vtype  v = TYPE_ITEM(vtype, x);               \
        MValue r = create_items(type_##rtype, n);                \
        for (index i = 0; i < n; i++)                            \
            r->rtype##s[i] =                                     \
                TYPE_FUNC(vtype, name)(v, TYPE_ITEMS(vtype, y)); \
        return r;                                                \
    }

#define CLAUSE_AA(name, rtype, vtype)                                       \
    IF_TYPE_B(vtype)                                                        \
        return create_##rtype(TYPE_FUNC(vtype, name)(TYPE_ITEM(vtype, x),   \
                                                     TYPE_ITEM(vtype, y)));



// clause list for plus, minus, times, divide_int and modulo
#define CLAUSES_PMM(clause, name)                \
    SHORTCUT(clause(name, int,     TAKE(int)))   \
             clause(name, int,     CONV(int))    \
    SHORTCUT(clause(name, long,    TAKE(long)))  \
             clause(name, long,    CONV(long))   \
    SHORTCUT(clause(name, float,   TAKE(float))) \
             clause(name, float,   CONV(float))

// primitive functions for plus, minus and times
#define INT_FUNC_PMM(name, vtype, op)                                \
static vtype##_type name##_##vtype(vtype##_type x, vtype##_type y) { \
    return is_null_##vtype(x) ? x : is_null_##vtype(y) ? y : x op y; \
}

#define FLOAT_FUNC_PMM(name, vtype, op)                              \
static vtype##_type name##_##vtype(vtype##_type x, vtype##_type y) { \
    return  x op y;                                                  \
}

// full verb definition for plus, minus, times, divide_int and modulo
#define VERB_PMM(name, rhs, op)          \
INT_FUNC_PMM  (name, int,   op)          \
INT_FUNC_PMM  (name, long,  op)          \
FLOAT_FUNC_PMM(name, float, op)          \
BINARY        (name, rhs,   CLAUSES_PMM)

VERB_PMM(plus,  left, +)
VERB_PMM(minus, neg,  -)
VERB_PMM(times, left, *)

SCALAR_BINARY(plus,  CLAUSES_PMM)
SCALAR_BINARY(minus, CLAUSES_PMM)


// clauses for divide
#define CLAUSES_D(clause, name)                  \
    SHORTCUT(clause(name, float,   TAKE(float))) \
             clause(name, float,   CONV(float))

// primitive functions for divide, divide_int and modulo
#define FLOAT_FUNC_D(name, vtype, func)                              \
static vtype##_type name##_##vtype(vtype##_type x, vtype##_type y) { \
    return func;                                                     \
}

// full verb definition for divide
FLOAT_FUNC_D(divide, float,  x / y)
BINARY      (divide, invert, CLAUSES_D)


Value entier(Value x) {
    if (IS_NUMERIC(x)) {
        if (x->type == type_float) {
            // note: assume float_type is double
            if (x->vector) {
                MValue r = create_items(type_float, x->count);
                for (index i = 0; i < x->count; i++)
                    r->floats[i] = floor(x->floats[i]);
                return r;
            } else
                return create_float(floor(x->_float));
        } else
            return x;
    }
    error(error_type);
}


// primitive functions for divide_int and modulo
#define INT_FUNC_DM(name, vtype, op)                                           \
static vtype##_type name##_##vtype(vtype##_type x, vtype##_type y) {           \
    if (y > 0)                                                                 \
        return x >= 0 ? x op y : is_null_##vtype(x) ? x : -(((y-1) - x) op y); \
    if (y == 0 || is_null_##vtype(y))                                          \
        return vtype##_null;                                                   \
    return x >= 0 ? -((x - (y+1)) op -y) : is_null_##vtype(x) ? x : -x op -y;  \
}

// full verb definition for divide_int and modulo
#define VERB_DM(name, rhs, op, func)    \
INT_FUNC_DM (name, int,   op)          \
INT_FUNC_DM (name, long,  op)          \
FLOAT_FUNC_D(name, float, func)        \
BINARY      (name, rhs,   CLAUSES_PMM)

VERB_DM(divide_int,  invert,           /, floor(x / y))
VERB_DM(modulo,      null_equivalent,  %, fmod(x, y))



// clause list for comparison verbs
#define CLAUSES_C(clause, vname)               \
             clause(vname, bool, TAKE(bool))   \
    SHORTCUT(clause(vname, bool, TAKE(byte)))  \
             clause(vname, bool, CONV(byte))   \
    SHORTCUT(clause(vname, bool, TAKE(int)))   \
             clause(vname, bool, CONV(int))    \
    SHORTCUT(clause(vname, bool, TAKE(long)))  \
             clause(vname, bool, CONV(long))   \
    SHORTCUT(clause(vname, bool, TAKE(float))) \
             clause(vname, bool, CONV(float))  \
             clause(vname, bool, TAKE(char))   \
             clause(vname, bool, TAKE(name))

// primitive functions comparison verbs
#define FUNC_C(vname, vtype, comp)                                 \
static bool_type vname##_##vtype(vtype##_type x, vtype##_type y) { \
    return compare_##vtype(x, y) comp 0;                           \
}

// full definition for comparison verbs
#define VERB_C(vname, comp)                    \
FUNC_C(vname, bool,  comp)                     \
FUNC_C(vname, byte,  comp)                     \
FUNC_C(vname, int,   comp)                     \
FUNC_C(vname, long,  comp)                     \
FUNC_C(vname, float, comp)                     \
FUNC_C(vname, char,  comp)                     \
FUNC_C(vname, name,  comp)                     \
BINARY(vname, null_bool_equivalent, CLAUSES_C)

static Value null_bool_equivalent(Value x) {
    if (x->vector) {
        if (x->type == type_variant) {
            MValue r = create_items(type_variant, x->count);
            for (index i = 0; i < x->count; i++)
                r->mixed[i] = null_bool_equivalent(x->mixed[i]);
            return r;
        } else {
            MValue r = create_items(type_bool, x->count);
            for (index i = 0; i < x->count; i++)
                r->bools[i] = -1;
            return r;
        }
    } else
        return create_bool(-1);
}

VERB_C(equal,       ==)
VERB_C(less,        < )
VERB_C(greater,     > )
VERB_C(not_equal,   !=)
VERB_C(not_less,    >=)
VERB_C(not_greater, <=)



// similarly for unary verbs
#define UNARY(name, clauses)                                   \
Value name(Value x) {                                          \
    if (x->vector) {                                           \
        index n = x->count;                                    \
        if (x->type == type_variant) {                         \
            MValue r = create_items(type_variant, n);          \
            for (index i = 0; i < n; i++)                      \
                r->mixed[i] = name(x->mixed[i]);               \
            return r;                                          \
        }                                                      \
        clauses(CLAUSE_V, name)                                \
    } else {                                                   \
        clauses(CLAUSE_A, name)                                \
        if (x->type == type_map)                               \
            return create_map(x->map.key, name(x->map.value)); \
    }                                                          \
    error(error_type);                                         \
}

#define IF_TYPE_U(vtype) if ((x->type  TYPE_COMP vtype  TYPE_NAME vtype))

#define CLAUSE_V(name, rtype, vtype)                          \
    IF_TYPE_U(vtype) {                                        \
        MValue r = create_items(type_##rtype, n);             \
        for (index i = 0; i < n; i++)                         \
            r->rtype##s[i] =                                  \
                TYPE_FUNC(vtype, name)(TYPE_ITEMS(vtype, x)); \
        return r;                                             \
    }

#define CLAUSE_A(name, rtype, vtype)                                        \
    IF_TYPE_U(vtype)                                                        \
        return create_##rtype(TYPE_FUNC(vtype, name)(TYPE_ITEM(vtype, x)));



// clauses for neg
#define CLAUSES_NEG(clause, name)               \
    SHORTCUT(clause(name, int,     TAKE(int)))  \
             clause(name, int,     CONV(int))   \
             clause(name, long,    TAKE(long))  \
             clause(name, float,   TAKE(float))

// primitive functions for neg, not and invert
#define INT_FUNC_NNI(name, rtype, vtype, op)         \
static vtype##_type name##_##vtype(vtype##_type x) { \
    return is_null_##vtype(x) ? rtype##_null : op x; \
}

#define FLOAT_FUNC_NI(name, vtype, op)               \
static vtype##_type name##_##vtype(vtype##_type x) { \
    return op x;                                     \
}

// full verb definition for neg
INT_FUNC_NNI (neg, int,   int,   -)
INT_FUNC_NNI (neg, long,  long,  -)
FLOAT_FUNC_NI(neg, float, -)
UNARY(neg, CLAUSES_NEG)


// clauses for not
#define CLAUSES_NOT(clause, name)               \
             clause(name, bool,    TAKE(bool))  \
             clause(name, bool,    TAKE(byte))  \
             clause(name, bool,    TAKE(int))   \
             clause(name, bool,    TAKE(long))  \
             clause(name, bool,    TAKE(float))

// full verb definition for not
INT_FUNC_NNI(not, bool, bool,  !)
INT_FUNC_NNI(not, bool, byte,  !)
INT_FUNC_NNI(not, bool, int,   !)
INT_FUNC_NNI(not, bool, long,  !)
INT_FUNC_NNI(not, bool, float, !) // yes, INT
UNARY(not, CLAUSES_NOT)


// full verb definition for invert
FLOAT_FUNC_NI(invert, float, 1 /)
UNARY(invert, CLAUSES_D)



// similarly for variadic verbs
#define VARIADIC(name, binary, init, func, clauses) \
Value name(Value x) {                               \
    if (x->vector) {                                \
        index n = x->count;                         \
        if (x->type == type_variant) {              \
            Value r = item_null(x, 0);              \
            for (index i = 1; i < x->count; i++)    \
                r = binary(r, x->mixed[i]);         \
            return r;                               \
        }                                           \
        clauses(CLAUSE_F, name, init, func)         \
    } else if (x->type == type_map)                 \
        return name(x->map.value);                  \
    else if (types[x->type].atomic)                 \
        return x;                                   \
    error(error_type);                              \
}

#define CLAUSE_F(name, init, func, rtype, vtype)       \
    IF_TYPE_U(vtype) {                                 \
        rtype##_type r = init(rtype);                  \
        for (index i = 0; i < n; i++) {                \
            TYPE_CTYPE vtype v = TYPE_ITEMS(vtype, x); \
            func(rtype, vtype);                        \
        }                                              \
        return create_##rtype(r);                      \
    }


// clause list for sum
#define CLAUSES_S(clause, name, init, func)               \
    SHORTCUT(clause(name, init, func, int,   TAKE(bool))) \
    SHORTCUT(clause(name, init, func, int,   TAKE(int)))  \
             clause(name, init, func, int,   CONV(int))   \
             clause(name, init, func, long,  TAKE(long))  \
             clause(name, init, func, float, TAKE(float))

// primitive functions for sum
#define INIT_ZERO(rtype) 0
#define FOLD_PLUS(rtype, vtype) {              \
    if (PASTE(is_null_, TYPE_TYPE vtype)(v)) { \
        r = rtype##_null;                      \
        break;                                 \
    }                                          \
    r += v;                                    \
}

// full verb definition for sum
VARIADIC(sum, plus, INIT_ZERO, FOLD_PLUS, CLAUSES_S)


// clause list for min and max
#define CLAUSES_MM(clause, name, init, func)              \
             clause(name, init, func, bool,  TAKE(bool))  \
             clause(name, init, func, byte,  TAKE(byte))  \
             clause(name, init, func, int,   TAKE(int))   \
             clause(name, init, func, long,  TAKE(long))  \
             clause(name, init, func, float, TAKE(float))

// primitive functions for min and max
#define INIT_MAX(rtype)  rtype##_max
#define INIT_MIN(rtype)  rtype##_min

#define FOLD_MIN(rtype, vtype) {               \
    if (PASTE(is_null_, TYPE_TYPE vtype)(v)) { \
        r = rtype##_null;                      \
        break;                                 \
    }                                          \
    if (v < r)                                 \
        r = v;                                 \
}

#define FOLD_MAX(rtype, vtype) \
    if (v > r)                 \
        r = v;

// full verb definition for min and max
VARIADIC(min, binary_min, INIT_MAX, FOLD_MIN, CLAUSES_MM)
VARIADIC(max, binary_max, INIT_MIN, FOLD_MAX, CLAUSES_MM)


Value primed_sum(Value x, Value y) {
    // fixme: possibly optimize
    return plus(x, sum(y));
}


Value primed_min(Value x, Value y) {
    // fixme: possibly optimize
    return binary_min(x, min(y));
}


Value primed_max(Value x, Value y) {
    // fixme: possibly optimize
    return binary_max(x, max(y));
}


Value variadic_plus(index n, const Value* p) {
    assert(n > 2);
    Value r = p[0];
    for (index i = 1; i < n; i++)
        r = plus(r, p[i]);
    return r;
}
