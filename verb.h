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

#ifndef VERB_H
#define VERB_H

#include "value.h"

enum {
    // normal verbs
    verb_null,
    verb_at,
    verb_dot,
    verb_comma,
    verb_hash,
    verb_line,
    verb_plus,
    verb_minus,
    verb_times,
    verb_divide,
    verb_bang,
    verb_and,
    verb_or,
    verb_tilde,
    verb_equal,
    verb_less,
    verb_greater,
    verb_hat,
    verb_query,
    verb_accent,
    verb_cast,
        verb_named_last = verb_cast,

    // unnamed verbs
    verb_list,
    verb_divide_int,
    verb_first,
    verb_not_equal,
    verb_not_less,
    verb_not_greater,
    verb_sum,
    verb_raze,
    verb_max,
    verb_min,
    verb_repr,
    verb_show,
    verb_lex,
    verb_parse,
    verb_disasm,
    verb_collect,
    verb_read,
    verb_write,
    verb_mmap,
    verb_time,
    verb_assign_item,
    verb_assign_element,

    // opcode-only verbs
    verb_global_read,
    verb_global_write,
    verb_init_counter,
    verb_init_closure,
    verb_scalar_plus,
    verb_scalar_minus
};


extern const struct verb {
    char name;
    struct value_verb literal_prime, literal;
} verbs[43];

extern const struct verb_run {
    Value (*unary)(Value);
    Value (*binary)(Value, Value);
    Value (*variadic)(index n, const Value*); // n > 2
    bool unary_collect; // reaches collector and should collect after use
    bool binary_collect;
} verbs_run[49];


Value left(Value);
Value right(Value, Value);
Value type(Value);

Value enlist(Value);
Value join(Value, Value);
Value variadic_join(index, const Value*);
Value raze(Value);

Value count(Value);
Value take(Value, Value);
Value drop(Value, Value);
Value flip(Value);
Value last(Value);
Value first(Value);
Value reverse(Value);

Value element(Value, Value);
Value bang(Value, Value);
Value value(Value);
Value range(Value);
Value where(Value);
Value group(Value);

Value order_asc(Value);
Value order_desc(Value);
Value unique(Value);
Value binary_min(Value, Value);
Value binary_max(Value, Value);
Value fill(Value, Value);
Value null(Value);

Value find(Value, Value);
Value identical(Value, Value);

Value compose(Value, Value);
Value cast(Value, Value);
Value throw(Value);
Value show(Value);

void globals_init();


#endif /* VERB_H */
