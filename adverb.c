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

#include "adverb.h"

#include "alloc.h"
#include "apply.h"
#include "error.h"
#include "func.h"
#include "verb.h"

#include <assert.h>
#include <limits.h>
#include <stdio.h>

#define index index_hide /* index() should be in string.h anyway */
#include <string.h>
#undef index


static Value rank_error(Value f, Value x) {
    error(error_rank);
}


static Value binary_error(Value f, Value x, Value y) {
    error(error_rank);
}


static Value variadic_error(Value f, index m, const Value* p) {
    error(error_rank);
}


static index unary_valence(Value f) {
    return 1;
}


static index binary_valence(Value f) {
    return 2;
}


static index alternative_valence(Value f) {
    return 2;
}


static index variable_valence(Value f) {
    return index_max;
}


static index verb_valence(Value f) {
    return valence(f);
}


static index verb_min_valence(Value f) {
    return min_valence(f);
}


static Value create_clause(Adverb adverb, Value verb) {
    MValue r = create_item(type_clause);
    r->clause.adverb = adverb;
    r->clause.verb = verb;
    return r;
}


Value each(Value f, Value x) {
    return create_clause(IS_INTEGER(x) ? adverb_each_select
                                       : adverb_each_call, x);
}


Value fold(Value f, Value x) {
    index v = valence(x);
    return create_clause(v == 1 ? adverb_repeat :
                         v == 2 ? adverb_binary_fold :
                                  adverb_variadic_fold, x);
}


Value scan(Value f, Value x) {
    index v = valence(x);
    return create_clause(v == 1 ? adverb_trace :
                         v == 2 ? adverb_binary_scan :
                                  adverb_variadic_scan, x);
}


Value each_right(Value f, Value x) {
    if (IS_CALLABLE(x)) {
        index v = valence(x);
        if (v != 2)
            error(error_rank);
        return create_clause(adverb_each_right_call, x);
    } else
        return create_clause(adverb_each_right_join, x);
}


Value each_left(Value f, Value x) {
    if (IS_CALLABLE(x)) {
        index v = valence(x);
        if (v != 2)
            error(error_rank);
        return create_clause(adverb_each_left_call, x);
    } else
        return create_clause(adverb_each_left_split, x);
}


Value each_pair(Value f, Value x) {
    switch (valence(x)) {
    case 1:
        return create_clause(adverb_each_pair_concurrent, x);
    case 2:
        return create_clause(adverb_each_pair_call, x);
    default:
        error(error_rank);
    }
}


Value scan_count(Value f, Value x) {
    index v = valence(x);
    return create_clause(v == 1 ? adverb_trace_count :
                         v == 2 ? adverb_binary_scan_count :
                                  adverb_variadic_scan_count, x);
}


#define IN_COLLECT COLLECT()

#define ECU_COUNT(n)   n = x->count;
#define ECU_CALL(v, i) v = apply(f, item(x, i));

Value each_call_unary(Value f, Value x) {
    if (!x->vector) {
        if (x->type == type_map)
            return create_map(x->map.key, each_call_unary(f, x->map.value));
        return apply(f, x); // VC pass
    }
    hold(f); hold(x);
    MValue r; hold_mvalue(&r);

    AUTO_STRENGTHEN(r, ECU_COUNT, ECU_CALL, ECU_CALL, IN_COLLECT)
    release_mvalue(1); release(2);
    return r;
}


#define ECB_COUNT(n)   n = x->vector ? x->count : y->count;
#define ECB_CALL(v, i) v = call_binary(f, x->vector ? item(x, i) : x,  \
                                          y->vector ? item(y, i) : y);

Value each_call_binary(Value f, Value x, Value y) {
    if (x->type == type_map || y->type == type_map) {
        if (x->type != type_map || y->type != type_map)
            error(error_type);

        // using a vector operation when keys are identical would be a
        // special case, not a shortcut, because keys might not be unique

        bool copied_key = 0;
        MValue r_key = (MValue)x->map.key;   hold_mvalue(&r_key);
        MValue r_value = copy(x->map.value); hold_mvalue(&r_value);
        for (index i = 0; i < y->map.key->count; i++) {
            Value v = item(y->map.value, i);
            Value k = item(y->map.key,   i);
            index j = find_item(r_key, k);
            v = call_binary(f, item_null(r_value, j), v);
            if (j < r_key->count)
                amend_weaken(&r_value, j, v);
            else {
                if (!copied_key) {
                    r_key = copy(r_key);
                    copied_key = 1;
                }
                push_weaken(&r_key, k);
                push_weaken(&r_value, v);
            }
        }
        release_mvalue(2);
        return create_map(r_key,
                          IS_MIXED(r_value) ? strengthen(r_value) : r_value);
    }

    if (!x->vector && !y->vector)
        return call_binary(f, x, y); // VC pass
    if (x->vector && y->vector && x->count != y->count)
        error(error_length);
    hold(f); hold(x); hold(y);
    MValue r; hold_mvalue(&r);

    AUTO_STRENGTHEN(r, ECB_COUNT, ECB_CALL, ECB_CALL, IN_COLLECT)
    release_mvalue(1); release(3);
    return r;
}


static index variadic_args_count(index m, const Value* p) {
    index n = -1;
    for (index j = 0; j < m; j++)
        if (p[j]->vector) {
            if (n < 0)
                n = p[j]->count;
            else if (n != p[j]->count)
                error(error_length);
        } else if (p[j]->type == type_map)
            error(error_type);
    return n;
}


#define ECV_COUNT(as_n) as_n = n;
#define ECV_CALL_FIRST(v, i)                           \
    Value args[m];                                     \
    for (index j = 0; j < m; j++)                      \
        args[j] = p[j]->vector ? item(p[j], 0) : p[j]; \
    v = call(f, m, args);

#define ECV_CALL(v, i)               \
    for (index j = 0; j < m; j++)    \
        if (p[j]->vector)            \
            args[j] = item(p[j], i); \
    v = call(f, m, args);

Value each_call_variadic(Value f, index m, const Value* p) {
    assert(m > 0);

    index n = variadic_args_count(m, p);
    if (n < 0)
        return call(f, m, p); // VC pass

    hold(f); hold_array(m, p);
    MValue r; hold_mvalue(&r);

    AUTO_STRENGTHEN(r, ECV_COUNT, ECV_CALL_FIRST, ECV_CALL, IN_COLLECT)
    release_mvalue(1); release_array(1); release(1);
    return r;
}


#define KEY_MOTION(key, call) {                      \
    Value km_key = (key); hold(km_key);              \
    Value km_value = (call);                         \
    release(1); return create_map(km_key, km_value); \
}

Value each_select_unary(Value f, Value x) {
    if (!f->vector) {
        if (f->type == type_map)
            KEY_MOTION(f->map.key, each_select_unary(f->map.value, x));
        return as_index(f) ? null_equivalent(x) : x;
    }
    if (!x->vector) {
        if (x->type == type_map)
            error(error_type);
        goto copy;
    }
    if (x->count != f->count)
        error(error_length);

#ifndef NSHORTCUT
    for (index i = 0; i < f->count; i++)
        if (item_as_index(f, i))
            goto copy;
    return x;
#endif

copy:;
    MValue r = x->vector ? copy(x) : replicate(x, f->count);
    if (r->type == type_variant) {
        for (index i = 0; i < f->count; i++)
            if (item_as_index(f, i))
                r->mixed[i] = null_equivalent(r->mixed[i]);
    } else {
        assert(types[r->type].atomic);
        size_t size = types[r->type].size;
        const char* null = (const char*)&types_conv[r->type].null;
        for (index i = 0; i < f->count; i++)
            if (item_as_index(f, i))
                COPY(r->items + size * i, null, size);
    }
    return r;
}


#define ES_COUNT(n)    n = f->count;
#define ESB_CALL(v, i)                                         \
    switch (item_as_index(f, i)) {                             \
    case 0:                                                    \
        v = x->vector ? item(x, i) : x;                        \
        break;                                                 \
    case 1:                                                    \
        v = y->vector ? item(y, i) : y;                        \
        break;                                                 \
    default:                                                   \
        v = x->vector ? item_null(x, -1) : null_equivalent(x); \
    }

Value each_select_binary(Value f, Value x, Value y) {
    if (!f->vector) {
        if (f->type == type_map)
            KEY_MOTION(f->map.key, each_select_binary(f->map.value, x, y));
        switch (as_index(f)) {
        case 0:  return x;
        case 1:  return y;
        default: return null_equivalent(x);
        }
    }

    if (x->vector && x->count != f->count || y->vector && y->count != f->count)
        error(error_length);
    if (x->type == type_map || y->type == type_map)
        error(error_type);

    // fixme: possibly optimize
    MValue r;
    AUTO_STRENGTHEN(r, ES_COUNT, ESB_CALL, ESB_CALL,)
    return r;
}


#define ESV_CALL(v, i) {                                                \
    index j = item_as_index(f, i);                                      \
    if (j >= 0 && j < n)                                                \
        v = p[j]->vector ? item(p[j], i) : p[j];                        \
    else                                                                \
        v = p[0]->vector ? item_null(p[0], -1) : null_equivalent(p[0]); \
}

Value each_select_variadic(Value f, index n, const Value* p) {
    assert(n > 0);
    if (!f->vector) {
        if (f->type == type_map)
            KEY_MOTION(f->map.key, each_select_variadic(f->map.value, n, p));
        index j = as_index(f);
        if (j >= 0 && j < n)
            return p[j];
        else
            return null_equivalent(p[0]);
    }

    for (index i = 0; i < n; i++) {
        if (p[i]->vector && p[i]->count != f->count)
            error(error_length);
        if (p[i]->type == type_map)
            error(error_type);
    }

    // fixme: possibly optimize
    MValue r;
    AUTO_STRENGTHEN(r, ES_COUNT, ESV_CALL, ESV_CALL,)
    return r;
}


Value changing(Value f, Value x) {
    hold(f);
    Value l; hold_array(1, &l);
    do {
        l = x;
        COLLECT();
        x = apply(f, l);
    } while (compare(x, l));
    release_array(1); release(1);
    return x;
}


Value trace_changing(Value f, Value x) {
    // fixme: strengthen automatically
    hold(f);
    MValue r = create_items(type_variant, 0); hold_mvalue(&r);
    Value l; hold_array(1, &l);
    do {
        l = x;
        COLLECT();
        push(&r, x = apply(f, l));
    } while (compare(x, l));
    release_array(1); release_mvalue(1); release(1);
    return strengthen(r);
}


Value trace_count_changing(Value f, Value x) {
    hold(f);
    index r = 0;
    Value l; hold_array(1, &l);
    do {
        l = x;
        COLLECT();
        x = apply(f, l), r++;
    } while (compare(x, l));
    release_array(1); release(1);
    return create_index(r);
}


#define LOOP(prefix, init, do_init, do_set, while_init, while_set, done, ret)  \
Value prefix##loop(Value f, Value x, Value y) {                                \
    hold(f);                                                                   \
    init;                                                                      \
    if (!x->vector && IS_NUMERIC(x)) {                                         \
        if (x->type < type_integer_first || x->type > type_integer_last)       \
            error(error_type);                                                 \
        index n = as_index(x);                                                 \
        do_init;                                                               \
        for (index i = 0; i < n; i++) {                                        \
            y = apply(f, y);                                                   \
            do_set;                                                            \
            COLLECT();                                                         \
        }                                                                      \
    } else {                                                                   \
        hold(x);                                                               \
        while_init;                                                            \
        while (as_condition(apply(x, y))) {                                    \
            y = apply(f, y);                                                   \
            while_set;                                                         \
            COLLECT();                                                         \
        }                                                                      \
        release(1);                                                            \
    }                                                                          \
    done;                                                                      \
    release(1);                                                                \
    return ret;                                                                \
}

LOOP(,,,,,,, y)
LOOP(trace_, MValue r; hold_mvalue(&r),
             r = create_items(type_variant, n), r->mixed[i] = y,
             r = create_items(type_variant, 0), push(&r, y),
             release_mvalue(1), strengthen(r))
LOOP(trace_count_, index r, r = n,, r = 0, r = add_length(r, 1),,
                   create_index(r))


Value binary_fold_unary(Value f, Value x) {
    if (!x->vector) {
        if (x->type == type_map)
            return binary_fold_unary(f, x->map.value);
        return x;
    }
    hold(f); hold(x);
    Value r = item_null(x, 0); hold_array(1, &r);
    for (index i = 1; i < x->count; i++) {
        r = call_binary(f, r, item(x, i));
        COLLECT();
    }
    release_array(1); release(2);
    return r;
}


Value binary_fold_binary(Value f, Value x, Value y) {
    if (!y->vector) {
        if (y->type == type_map)
            return binary_fold_binary(f, x, y->map.value);
        return call_binary(f, x, y);
    }
    hold(f); hold(y);
    Value r = x; hold_array(1, &r);
    for (index i = 0; i < y->count; i++) {
        r = call_binary(f, r, item(y, i)); // c. pass r
        COLLECT();
    }
    release_array(1); release(2);
    return r;
}


Value fold_variadic(Value f, index m, const Value* p) {
    assert(m > 1);

    index n = variadic_args_count(m - 1, p + 1);
    if (n < 0)
        return call(f, m, p); // c. pass
    hold(f); hold_array(m, p);

    Value args[m]; hold_array(1, &args[0]);
    COPIES(args, p, sizeof *p, m);
    for (index i = 0; i < n; i++) {
        for (index j = 1; j < m; j++)
            if (p[j]->vector)
                args[j] = item(p[j], i);
                // c.: those not overwritten are accounted in p
        args[0] = call(f, m, args);
        COLLECT();
    }
    release_array(2); release(1);
    return args[0];
}


#define BSU_COUNT(n)         n = y->count - 1;
#define BSU_CALL_FIRST(v, i) x = item(y, 0); BSU_CALL(v, i)
#define BSU_CALL(v, i)       x = v = call_binary(f, x, item(y, (i)+1));

Value binary_scan_unary(Value f, Value y) {
    if (!y->vector) {
        if (y->type == type_map)
            error(error_type);
        return y;
    }
    hold(f); hold(y);
    MValue r; Value x; hold_mvalue(&r); hold_array(1, &x);

    AUTO_STRENGTHEN(r, BSU_COUNT, BSU_CALL_FIRST, BSU_CALL, IN_COLLECT)
    release_array(1); release_mvalue(1); release(2);
    return r;
}


#define BSB_COUNT(n)   n = y->count;
#define BSB_CALL(v, i) x = v = call_binary(f, x, item(y, i));

Value binary_scan_binary(Value f, Value x, Value y) {
    if (!y->vector) {
        if (y->type == type_map)
            KEY_MOTION(f->map.key, binary_scan_binary(f->map.value, x, y));
        return call_binary(f, x, y);
    }
    hold(f); hold(y); hold_array(1, &x);
    MValue r; hold_mvalue(&r);

    AUTO_STRENGTHEN(r, BSB_COUNT, BSB_CALL, BSB_CALL, IN_COLLECT)
    release_mvalue(1); release_array(1); release(2);
    return r;
}


#define SV_COUNT(as_n) as_n = n;
#define SV_CALL(v, i)                \
    for (index j = 1; j < m; j++)    \
        if (p[j]->vector)            \
            args[j] = item(p[j], i); \
    args[0] = v = call(f, m, args);

Value scan_variadic(Value f, index m, const Value* p) {
    assert(m > 1);

    index n = variadic_args_count(m - 1, p + 1);
    if (n < 0)
        return call(f, m, p); // c. pass
    hold(f); hold_array(m - 1, p + 1);

    Value args[m]; hold_array(1, &args[0]);
    args[0] = p[0];
    for (index j = 1; j < m; j++)
        if (!p[j]->vector)
            args[j] = p[j];

    MValue r; hold_mvalue(&r);
    AUTO_STRENGTHEN(r, SV_COUNT, SV_CALL, SV_CALL, IN_COLLECT)
    release_mvalue(1); release_array(2); release(1);
    return r;
}


#define MAX(x, y) ((x) > (y) ? (x) : (y))

Value binary_scan_count_unary(Value f, Value y) {
    index r;
    if (!y->vector) {
        if (y->type == type_map)
            error(error_type);
        r = 1;
    } else {
        r = MAX(0, y->count-1);
        binary_fold_unary(f, y); // c. pass
    }
    return create_index(r);
}


Value binary_scan_count_binary(Value f, Value x, Value y) {
    index r;
    if (!y->vector) {
        if (y->type == type_map)
            return binary_scan_count_binary(f, x, y->map.value);
        r = 1;
        call_binary(f, x, y); // c. pass
    } else {
        r = y->count;
        binary_fold_binary(f, x, y); // c. pass
    }
    return create_index(r);
}


Value scan_count_variadic(Value f, index m, const Value* p) {
    assert(m > 1);

    index r;
    index n = variadic_args_count(m - 1, p + 1);
    if (n < 0) {
        r = 1;
        call(f, m, p); // c. pass
    } else {
        r = n;
        fold_variadic(f, m, p); // c. pass
    }
    return create_index(r);
}


#define ERC_COUNT(n)   n = y->count;
#define ERC_CALL(v, i) v = call_binary(f, x, item(y, i));

Value each_right_call(Value f, Value x, Value y) {
    if (!y->vector) {
        if (y->type == type_map)
            KEY_MOTION(y->map.key, each_right_call(f, x, y->map.value));
        return call_binary(f, x, y); // c. pass
    }
    hold(f); hold(x); hold(y);
    MValue r; hold_mvalue(&r);

    AUTO_STRENGTHEN(r, ERC_COUNT, ERC_CALL, ERC_CALL, IN_COLLECT)
    release_mvalue(1); release(3);
    return r;
}


#define ELC_COUNT(n)   n = x->count;
#define ELC_CALL(v, i) v = call_binary(f, item(x, i), y);

Value each_left_call(Value f, Value x, Value y) {
    if (!x->vector) {
        if (x->type == type_map)
            KEY_MOTION(x->map.key, each_left_call(f, x->map.value, y));
        return call_binary(f, x, y); // c. pass
    }
    hold(f); hold(x); hold(y);
    MValue r; hold_mvalue(&r);

    AUTO_STRENGTHEN(r, ELC_COUNT, ELC_CALL, ELC_CALL, IN_COLLECT)
    release_mvalue(1); release(3);
    return r;
}


Value each_right_join(Value x, Value y) {
    if (y->vector) {
        // join with separator
        Type type = x->type;
        if (!types[type].vectorable || !IS_MIXED(y) && y->type != x->type)
            error(error_type);
        index x_count = x->vector ? x->count : 1;

        index n = 0;
        for (index i = 0; i < y->count; i++) {
            if (i)
                n = add_length(n, x_count);
            if (IS_MIXED(y)) {
                Value v = y->mixed[i];
                if (v->type != type)
                    error(error_type);
                index c = v->vector ? v->count : 1;
                n = add_length(n, c);
            } else
                n = add_length(n, 1);
        }

        size_t size =  types[type].size;
        short offset = types[type].offset;
        const char* x_items = x->vector ? x->items : x->item + offset;
        MValue r = create_items(type, n);
        n = 0;
        for (index i = 0; i < y->count; i++) {
            if (i) {
                COPIES(r->items + size * n, x_items, size, x_count);
                n += x_count;
            }
            if (IS_MIXED(y)) {
                Value v = y->mixed[i];
                index c = v->vector ? v->count : 1;
                COPIES(r->items + size * n,
                       v->vector ? v->items : v->item + offset, size, c);
                n += c;
            } else
                COPY(r->items + size * n++, y->items + size * i, size);
        }
        assert(n == r->count);
        return r;
    } else
        error(error_type);
}


Value each_left_split(Value x, Value y) {
    if (y->vector) {
        if (x->type != y->type)
            error(error_type);

        // todo: equality comparison can be done by memcmp for most types
        size_t size = types[x->type].size;
        int (*compare)(const char*, const char*) = types_conv[x->type].compare;

        MValue r = create_items(type_variant, 0);
        if (x->vector) {
            // split on elements
            if (!x->count)
                error(error_length);

            for (index i = 0;;) {
                for (index j = i; j + x->count <= y->count; j++) {
                    for (index k = 0; k < x->count; k++)
                        if (compare(y->items + size * (j + k),
                                    x->items + size * k))
                            goto different;
                    push(&r, subvector(y, i, j - i));
                    i = j + x->count;
                    goto next_sequence;
                different:;
                }
                push(&r, subvector(y, i, y->count - i));
                break;
            next_sequence:;
            }
        } else {
            // split on arbitrary runs of element
            short offset = types[x->type].offset;
            for (index i = 0;;) {
                for (index j = i; j < y->count; j++)
                    if (!compare(y->items + size * j, x->item + offset)) {
                        push(&r, subvector(y, i, j - i));
                        for (j++; j < y->count; j++)
                            if (compare(y->items + size * j, x->item + offset))
                                break;
                        i = j;
                        goto next_run;
                    }
                push(&r, subvector(y, i, y->count - i));
                break;
            next_run:;
            }
        }
        return r;
    } else {
        // digits
        if (!x->vector && x->type == type_int && x->_int > 1) {
            long_type l;
            switch (y->type) {
            case type_int:  l = y->_int; break;
            case type_long: l = y->_long; break;
            default: error(error_type);
            }
            if (l < 0)
                error(error_range);
            int d = 0;
            for (long_type v = l; v; v /= x->_int)
                d++;
            MValue r = create_items(type_int, d);
            while (d > 0) {
                r->ints[--d] = l % x->_int;
                l /= x->_int;
            }
            return r;
        } else
            error(error_type);
    }
}


#define EPCU_COUNT(n)         n = y->count - 1;
#define EPCU_CALL_FIRST(v, i) x = item(y, 0); EPCU_CALL(v, i)
#define EPCU_CALL(v, i)       Value l = x; x = item(y, (i)+1); \
                              v = call_binary(f, x, l);

Value each_pair_call_unary(Value f, Value y) {
    if (!y->vector) {
        if (y->type == type_map)
            error(error_type);
        return call_binary(f, y, y); // c. pass
    }
    hold(f); hold(y);
    MValue r; Value x; hold_mvalue(&r); hold_array(1, &x);

    AUTO_STRENGTHEN(r, EPCU_COUNT, EPCU_CALL_FIRST, EPCU_CALL, IN_COLLECT)
    release_array(1); release_mvalue(1); release(2);
    return r;
}


#define EPCB_COUNT(n)   n = y->count;
#define EPCB_CALL(v, i) Value l = x; x = item(y, i); v = call_binary(f, x, l);

Value each_pair_call_binary(Value f, Value x, Value y) {
    if (!y->vector) {
        if (y->type == type_map)
            KEY_MOTION(y->map.key, each_pair_call_binary(f, x, y->map.value));
        return call_binary(f, x, y); // c. pass
    }
    hold(f); hold(y); hold_array(1, &x);
    MValue r; hold_mvalue(&r);

    AUTO_STRENGTHEN(r, EPCB_COUNT, EPCB_CALL, EPCB_CALL, IN_COLLECT)
    release_mvalue(1); release_array(1); release(2);
    return r;
}


Value each_pair_concurrent(Value f, Value x) {
    error(error_todo);
}


#define LITERAL(name) { type_clause, 0, { adverb_##name } }

const struct adverb adverbs[] = {
    // adverb names
    { '\'', 0, unary_valence, unary_valence, LITERAL(each)       },
    { '/',  0, unary_valence, unary_valence, LITERAL(fold)       },
    { '\\', 0, unary_valence, unary_valence, LITERAL(scan)       },
    { '/',  1, unary_valence, unary_valence, LITERAL(each_right) },
    { '\\', 1, unary_valence, unary_valence, LITERAL(each_left)  },
    { '\'', 1, unary_valence, unary_valence, LITERAL(each_pair)  },

    // clause equivalents
    { 0,    0, unary_valence, unary_valence, LITERAL(scan_count) },

    // adverbs by type
    { 0,    0, verb_valence,        verb_min_valence },
    { 0,    0, variable_valence,    unary_valence    },
    { 0,    0, alternative_valence, unary_valence    },
    { 0,    0, alternative_valence, unary_valence    },
    { 0,    0, verb_valence,        verb_min_valence },
    { 0,    0, alternative_valence, unary_valence    },
    { 0,    0, alternative_valence, unary_valence    },
    { 0,    0, alternative_valence, unary_valence    },
    { 0,    0, verb_valence,        verb_min_valence },
    { 0,    0, alternative_valence, unary_valence    },
    { 0,    0, verb_valence,        verb_min_valence },
    { 0,    0, binary_valence,      binary_valence   },
    { 0,    0, unary_valence,       unary_valence    },
    { 0,    0, binary_valence,      binary_valence   },
    { 0,    0, unary_valence,       unary_valence    },
    { 0,    0, binary_valence,      unary_valence    },
    { 0,    0, unary_valence,       unary_valence    }
};


const struct adverb_run adverbs_run[] = {
    // adverb names
    { each,                    binary_error,             variadic_error       },
    { fold,                    binary_error,             variadic_error       },
    { scan,                    binary_error,             variadic_error       },
    { each_right,              binary_error,             variadic_error       },
    { each_left,               binary_error,             variadic_error       },
    { each_pair,               binary_error,             variadic_error       },

    // clause equivalents
    { scan_count,              binary_error,             variadic_error       },

    // adverbs by type
    { each_call_unary,         each_call_binary,         each_call_variadic   },
    { each_select_unary,       each_select_binary,       each_select_variadic },
    { changing,                loop,                     variadic_error       },
    { binary_fold_unary,       binary_fold_binary,       variadic_error       },
    { rank_error,              binary_error,             fold_variadic        },
    { trace_changing,          trace_loop,               variadic_error       },
    { trace_count_changing,    trace_count_loop,         variadic_error       },
    { binary_scan_unary,       binary_scan_binary,       variadic_error       },
    { rank_error,              binary_error,             scan_variadic        },
    { binary_scan_count_unary, binary_scan_count_binary, variadic_error       },
    { rank_error,              binary_error,             scan_count_variadic  },
    { rank_error,              each_right_call,          variadic_error       },
    { each_right_join,         binary_error,             variadic_error       },
    { rank_error,              each_left_call,           variadic_error       },
    { each_left_split,         binary_error,             variadic_error       },
    { each_pair_call_unary,    each_pair_call_binary,    variadic_error       },
    { each_pair_concurrent,    binary_error,             variadic_error       }
};
