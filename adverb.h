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

#ifndef ADVERB_H
#define ADVERB_H

#include "value.h"

enum {
    // adverb names
    adverb_each,
    adverb_fold,
    adverb_scan,
    adverb_each_right,
    adverb_each_left,
    adverb_each_pair,
        adverb_named_last = adverb_each_pair,

    // clause equivalents
    adverb_scan_count,

    // adverbs by type
    adverb_each_call,
    adverb_each_select,
    adverb_repeat,
    adverb_binary_fold,
    adverb_variadic_fold,
    adverb_trace,
    adverb_trace_count,
    adverb_binary_scan,
    adverb_variadic_scan,
    adverb_binary_scan_count,
    adverb_variadic_scan_count,
    adverb_each_right_call,
    adverb_each_right_join,
    adverb_each_left_call,
    adverb_each_left_split,
    adverb_each_pair_call,
    adverb_each_pair_concurrent
};


extern const struct adverb {
    char name;
    bool colon;
    index (*valence)(Value verb);
    index (*min_valence)(Value verb);
    struct value_clause literal;
} adverbs[24];

extern const struct adverb_run {
    Value (*unary)(Value, Value);
    Value (*binary)(Value, Value, Value);
    Value (*variadic)(Value, index n, const Value*); // n > 2
} adverbs_run[24];


Value each(Value, Value);
Value fold(Value, Value);
Value scan(Value, Value);
Value each_right(Value, Value);
Value each_left(Value, Value);
Value each_pair(Value, Value);
Value scan_count(Value, Value);
Value each_call_unary(Value, Value);
Value each_call_binary(Value, Value, Value);
Value each_call_variadic(Value, index, const Value*);
Value each_select_unary(Value, Value);
Value each_select_binary(Value, Value, Value);
Value each_select_variadic(Value, index, const Value*);
Value changing(Value, Value);
Value trace_changing(Value, Value);
Value trace_count_changing(Value, Value);
Value loop(Value, Value, Value);
Value trace_loop(Value, Value, Value);
Value trace_count_loop(Value, Value, Value);
Value binary_fold_unary(Value, Value);
Value binary_fold_binary(Value, Value, Value);
Value variadic_fold(Value, index, const Value*);
Value binary_scan_unary(Value, Value);
Value binary_scan_binary(Value, Value, Value);
Value variadic_scan(Value, index, const Value*);
Value binary_scan_count_unary(Value, Value);
Value binary_scan_count_binary(Value, Value, Value);
Value variadic_scan_count(Value, index, const Value*);
Value each_right_call(Value, Value, Value);
Value each_left_call(Value, Value, Value);
Value each_right_join(Value, Value);
Value each_left_split(Value, Value);
Value each_pair_call_unary(Value, Value);
Value each_pair_call_binary(Value, Value, Value);
Value each_pair_concurrent(Value, Value);


// note: r is accounted by the user
#define AUTO_STRENGTHEN(r, count, call_first, call, inner) {                  \
    index as_n;                                                               \
    count(as_n)                                                               \
    if (as_n <= 0)                                                            \
        r = (MValue)&empty;                                                   \
    else {                                                                    \
        Value as_v; index as_i = 0;                                           \
        call_first(as_v, as_i)                                                \
        Type as_type = as_v->type;                                            \
        if (as_v->vector || !types[as_type].vectorable) {                     \
            r = create_items(type_variant, as_n);                             \
            goto as_mixed;                                                    \
        }                                                                     \
        size_t as_size = types[as_type].size;                                 \
        short as_offset = types[as_type].offset;                              \
        r = create_items(as_type, as_n);                                      \
        goto as_vector;                                                       \
                                                                              \
        for (; as_i < as_n; as_i++) {                                         \
            inner;                                                            \
            call(as_v, as_i)                                                  \
            if (as_v->vector || as_v->type != as_type) {                      \
                r = weaken_to(r, as_i);                                       \
                goto as_mixed;                                                \
            }                                                                 \
        as_vector:                                                            \
            COPY(r->items + as_size * as_i, as_v->item + as_offset, as_size); \
        }                                                                     \
        goto as_done;                                                         \
                                                                              \
        for (; as_i < as_n; as_i++) {                                         \
            inner;                                                            \
            call(as_v, as_i);                                                 \
        as_mixed:                                                             \
            r->mixed[as_i] = as_v;                                            \
        }                                                                     \
                                                                              \
    as_done:;                                                                 \
    }                                                                         \
}


#endif /* ADVERB_H */
