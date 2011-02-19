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

#include "func.h"

#include "adverb.h"
#include "alloc.h"
#include "apply.h"
#include "code.h"
#include "error.h"
#include "parse.h"
#include "string.h"
#include "verb.h"

#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>

#define index index_hide /* index() should be in string.h anyway */
#include <string.h>
#undef index


// regs:
// 0*PART: frame: [self] [args] [closure] [free locals] [temps]
// 1*PART: closed locals
// 2*PART: upvalues
// 3*PART: literals (last is NULL if use_null)

// code:
// [0*PART+verb, res, arg, arg]:                         binary verb
// [1*PART+verb, res, arg]:                              unary verb
// [2*PART+(number-2)+partial*PART/2, res, arg, arg...]: call
// [3*PART+0, arg]:                                      return
// [3*PART+1, ip]:                                       jmp
// [3*PART+2, ip, arg]:                                  jz
// [3*PART+3, ip, arg]:                                  dec and jle

struct cf_state {
    int pass; // 1 = count locals, auto args
              // 2 = count globals, generate literals (including subfunctions)
              // 3 = generate code
    struct cf_state* scope;
    instr_word* instr;
    instr_word ip;
    MValue temps;         // bools
    MValue args;          // names, some possibly null
    MValue free_locals;   // names, excluding enclosed
    MValue closed_locals; // names
    MValue closed_init;   // names, subset of closed_locals
    MValue assigned;      // names (both free and closed locals)
    MValue scalars;       // indexes (code words)
    MValue literals;      // mixed // todo: sort by accesses before pass 3
    index literal_func;
    bool use_upvalues;
    bool use_null;
    bool auto_args;
};


static instr_word cf_literal(struct cf_state* state, Value literal) {
    if (state->pass >= 2) {
        index i =
            literal->type == type_func ? state->literals->count
                                       : find_item(state->literals, literal);
        if (i >= INSTR_PART-1) // 1 for possible NULL at end
            error(error_literals);
        if (i == state->literals->count) {
            if (state->pass > 2)
                assert_failed("literal appeared after pass 2");
            push(&state->literals, literal);
        }

        instr_word r = 3*INSTR_PART + i;
        if (!literal->vector && literal->type != type_map &&
                !IS_CALLABLE(literal))
            insert(&state->scalars, create_index(r));
        return r;
    } else
        return 0;
}


static instr_word cf_temp(struct cf_state* state) {
    if (state->pass >= 3) {
        index i = insert(&state->temps, create_bool(0));
        amend(&state->temps, create_index(i), create_bool(1));
        i = 1 + state->args->count + !!state->closed_locals->count +
                state->free_locals->count + i;
        if (i >= INSTR_PART)
            error(error_temps);
        return i;
    } else
        return 0;
}


static instr_word cf_temp_base(struct cf_state* state) {
    return 1 + state->args->count + !!state->closed_locals->count +
               state->free_locals->count;
}


static void cf_free(struct cf_state* state, instr_word x) {
    if (state->pass >= 3) {
        instr_word base = cf_temp_base(state);
        if (x >= base && x < INSTR_PART) {
            x -= base;
            if (x >= state->temps->count)
                assert_failed("free temp that is out of range");
            if (!state->temps->bools[x])
                assert_failed("free temp that is not in use");
            amend(&state->temps, create_index(x), create_bool(0));
        }
    }
}


static index cf_auto_arg(struct cf_state* state, Value var) {
    static Value* names[] = { &name_x, &name_y, &name_z };
    for (index i = 0; i < sizeof names / sizeof *names; i++)
        if (var->_name == (*names[i])->_name) {
            for (index j = state->args->count; j <= i; j++)
                push(&state->args, *names[j]);
            return 1 + i;
        }
    return -1;
}


static bool find_item_check(index* i, Value x, Value y) {
    assert(x->vector);
    index j = find_item(x, y);
    if (j < x->count) {
        *i = j;
        return 1;
    } else
        return 0;
}


static instr_word cf_name_read(struct cf_state* state, Value var) {
    // returns 0 for global
    assert(var->type == type_name);
    if (state->pass == 1) {
        if (state->scope && state->auto_args)
            cf_auto_arg(state, var);
        return 1;
    } else {
        if (state->scope) {
            index i;
            if (find_item_check(&i, state->args, var))
                return 1 + i;
            if (find_item_check(&i, state->free_locals, var) &&
                        in(state->assigned, var))
                return 1 + state->args->count + !!state->closed_locals->count +
                       i;
            if (find_item_check(&i, state->closed_locals, var) &&
                        in(state->assigned, var))
                return INSTR_PART + i;
            if (find_item_check(&i, state->scope->args, var)) {
                state->use_upvalues = 1;
                i = insert(&state->scope->closed_locals, var);
                if (i >= INSTR_PART)
                    error(error_locals);
                return 2*INSTR_PART + i;
            }
            if (find_item_check(&i, state->scope->closed_locals, var)) {
                state->use_upvalues = 1;
                if (!in(state->scope->assigned, var))
                    insert(&state->scope->closed_init, var);
                return 2*INSTR_PART + i;
            }
            if (find_item_check(&i, state->scope->free_locals, var)) {
                state->use_upvalues = 1;
                if (!in(state->scope->assigned, var))
                    insert(&state->scope->closed_init, var);
                delete(&state->scope->free_locals, i);
                i = insert(&state->scope->closed_locals, var);
                if (i >= INSTR_PART)
                    error(error_locals);
                return 2*INSTR_PART + i;
            }
        }
        return 0;
    }
}


static instr_word cf_name_write(struct cf_state* state, Value var, bool local) {
    // returns 0 for global
    assert(var->type == type_name);
    if (local) {
        if (state->scope) {
            index i;
            if (find_item_check(&i, state->args, var))
                return 1 + i;
            if (find_item_check(&i, state->closed_locals, var))
                return INSTR_PART + i;
            i = 1 + state->args->count + !!state->closed_locals->count +
                    insert(&state->free_locals, var);
            if (i >= INSTR_PART)
                error(error_locals);
            return i;
        }
    } else {
        if (state->pass >= 2) {
            if (state->scope) {
                index i;
                if (find_item_check(&i, state->scope->closed_locals, var)) {
                    state->use_upvalues = 1;
                    return 2*INSTR_PART + i;
                }
                if (find_item_check(&i, state->scope->free_locals, var)) {
                    state->use_upvalues = 1;
                    delete(&state->scope->free_locals, i);
                    i = insert(&state->scope->closed_locals, var);
                    if (i >= INSTR_PART)
                        error(error_locals);
                    return 2*INSTR_PART + i;
                }
            }
        }
    }
    return 0;
}


static void cf_emit_reserve(struct cf_state* state, size_t n) {
    // ip = INSTR_LAST is reserved
    if (state->ip > INSTR_LAST - n)
        error(error_code);
    state->instr = resize_alloc(state->instr,
                                sizeof *state->instr * (state->ip + n));
}


static void cf_emit_2(struct cf_state* state, instr_word w1, instr_word w2) {
    if (state->pass == 3) {
        cf_emit_reserve(state, 2);
        state->instr[state->ip++] = w1;
        state->instr[state->ip++] = w2;
    }
}


static void cf_emit_3(struct cf_state* state,
                      instr_word w1, instr_word w2, instr_word w3) {
    if (state->pass == 3) {
        cf_emit_reserve(state, 3);
        state->instr[state->ip++] = w1;
        state->instr[state->ip++] = w2;
        state->instr[state->ip++] = w3;
    }
}


static void cf_emit_4(struct cf_state* state,
                      instr_word w1, instr_word w2,
                      instr_word w3, instr_word w4) {
    if (state->pass == 3) {
        cf_emit_reserve(state, 4);
        state->instr[state->ip++] = w1;
        state->instr[state->ip++] = w2;
        state->instr[state->ip++] = w3;
        state->instr[state->ip++] = w4;
    }
}


static void cf_emit_set(struct cf_state* state, instr_word r, instr_word x) {
    cf_emit_3(state, INSTR_PART + verb_null, r, x);
}


#define ABS(x) ((x) < 0 ? -(x) : (x))

static bool cf_is_constant(Value x) {
    if (IS_NUMERIC(x))
        return 1;
    switch (x->type) {
    case type_verb_prime:
    case type_verb:
        return 1;
    case type_clause:
        return !x->clause.verb || cf_is_constant(x->clause.verb);
    }
    return 0;
}


static bool cf_transform_match_compose(Value tree, Verb result_verb,
                                       bool prime, Verb verb) {
    assert(IS_MIXED(tree) && tree->count >= 2);
    return tree->count == 2 &&
           tree->mixed[0]->type == type_verb_prime &&
           tree->mixed[0]->verb == result_verb &&
  IS_MIXED(tree->mixed[1]) &&
           tree->mixed[1]->count == 2 + !prime &&
           tree->mixed[1]->mixed[0]->type ==
               (prime ? type_verb_prime : type_verb) &&
          (tree->mixed[1]->mixed[0]->verb == verb || verb == verb_null);
}


static Value cf_transform(Value tree) {
    if (!IS_MIXED(tree) || tree->count < 2)
        return tree;
    Value head = tree->mixed[0];

    if (head->type == type_clause && tree->count == 2) {
        Value verb = cf_transform(tree->mixed[1]);
        if (verb != tree->mixed[1] || cf_is_constant(verb))
            return adverbs_run[head->clause.adverb].unary(head, verb);

    } else if (IS_MIXED(head) && head->count == 2 && tree->count == 2 &&
               head->mixed[0]->type == type_clause &&
                   head->mixed[0]->clause.adverb == adverb_fold &&
               head->mixed[1]->type == type_verb)
        switch (head->mixed[1]->verb) {
        Verb verb;
        case verb_plus:  verb = verb_sum;  goto fold_verb;
        case verb_and:   verb = verb_min;  goto fold_verb;
        case verb_or:    verb = verb_max;  goto fold_verb;
        case verb_comma: verb = verb_raze; goto fold_verb;
        fold_verb:
            return cons((Value)&verbs[verb].literal_prime,
                        cf_transform(tree->mixed[1]));
        }

    // replacements match those in compose()
    else if (cf_transform_match_compose(tree, verb_line, 0, verb_divide))
        return triplet((Value)&verbs[verb_divide_int].literal,
                       cf_transform(tree->mixed[1]->mixed[1]),
                       cf_transform(tree->mixed[1]->mixed[2]));

    else if (cf_transform_match_compose(tree, verb_times, 1, verb_or))
        return cons((Value)&verbs[verb_first].literal_prime,
                     cf_transform(tree->mixed[1]->mixed[1]));

    else if (cf_transform_match_compose(tree, verb_tilde, 0, verb_null))
        switch (tree->mixed[1]->mixed[0]->verb) {
        Verb verb;
        case verb_equal:   verb = verb_not_equal;   goto not_verb;
        case verb_less:    verb = verb_not_less;    goto not_verb;
        case verb_greater: verb = verb_not_greater; goto not_verb;
        not_verb:
            return triplet((Value)&verbs[verb].literal,
                           cf_transform(tree->mixed[1]->mixed[1]),
                           cf_transform(tree->mixed[1]->mixed[2]));
        }

    else if (head->type == type_verb_prime &&
             head->verb == verb_hash && tree->count == 2 &&
    IS_MIXED(tree->mixed[1]) &&
             tree->mixed[1]->count > 1 &&
    IS_MIXED(tree->mixed[1]->mixed[0]) &&
             tree->mixed[1]->mixed[0]->count == 2 &&
             tree->mixed[1]->mixed[0]->mixed[0]->type == type_clause &&
             tree->mixed[1]->mixed[0]->mixed[0]->clause.adverb == adverb_scan) {
        MValue r = create_items(type_variant, tree->mixed[1]->count);
        r->mixed[0] = cons((Value)&adverbs[adverb_scan_count].literal,
                           tree->mixed[1]->mixed[0]->mixed[1]);
        for (index i = 1; i < r->count; i++)
            r->mixed[i] = tree->mixed[1]->mixed[i];
        return r;
    }

    else if (head->type == type_verb && head->verb == verb_list &&
             tree->count > 2 && (tree->count-1) - 2 >= INSTR_PART / 2) {
        for (index i = 1; i < tree->count; i++)
            if (IS_NULL(tree->mixed[i]))
                goto skip_split_list;

        index n = (tree->count-1 + (INSTR_PART / 2 + 1 - 1)) /
                                   (INSTR_PART / 2 + 1);
        MValue r = create_items(type_variant, 1 + n);
        r->mixed[0] = (Value)&verbs[verb_comma].literal;
        for (index i = 0; i < n; i++) {
            index k = i *      (INSTR_PART / 2 + 1);
            index m = i < n-1 ? INSTR_PART / 2 + 1 : (tree->count-1) - k;
            MValue v = create_items(type_variant, 1 + m);
            v->mixed[0] = head;
            for (index j = 0; j < m; j++)
                v->mixed[1+j] = tree->mixed[1+k+j];
            r->mixed[1+i] = v;
        }
        return r;

    skip_split_list:;
    }

    return tree; // todo: more rules
}


static instr_word cf_recurse(struct cf_state* state,
                             Value tree, instr_word dest);

static instr_word cf_recurse_cond(struct cf_state* state,
                                  Value tree, instr_word dest, index i) {
    assert(IS_MIXED(tree) && tree->count % 2 == 0 && i + 3 <= tree->count);

    instr_word c = cf_recurse(state, tree->mixed[i], 0);
    cf_free(state, c);
    cf_emit_3(state, 3*INSTR_PART + 2, 0, c);
    instr_word target_c = state->ip - 2, target_x = 0;
    if (state->pass == 3 && c <= 1 + state->args->count)
        push(&state->scalars, create_index(c));

    instr_word r = INSTR_LAST;
    MValue assigned_c = copy(state->assigned);
    instr_word x = cf_recurse(state, tree->mixed[i+1], dest);
    if (x != INSTR_LAST)
        if (dest == INSTR_LAST)
            cf_emit_2(state, 3*INSTR_PART + 0, x);
        else if (x >= cf_temp_base(state) && x < INSTR_PART)
            r = x;
        else {
            r = cf_temp(state);
            cf_free(state, x);
            cf_emit_set(state, r, x);
        }

    if (r != INSTR_LAST) {
        cf_emit_2(state, 3*INSTR_PART + 1, 0);
        target_x = state->ip - 1;
    }
    if (state->pass == 3)
        state->instr[target_c] = state->ip;

    MValue assigned_x = state->assigned;
    state->assigned = assigned_c;
    if (dest != INSTR_LAST && r != INSTR_LAST)
        dest = x;
    // ideally we should tell both the fact that dest == INSTR_LAST and the
    // value of r to the function
    instr_word y =
        i + 3 < tree->count ? cf_recurse_cond(state, tree, dest, i + 2)
                            : cf_recurse(state, tree->mixed[i+2], dest);
    if (y != INSTR_LAST) {
        if (r == INSTR_LAST)
            r = y;
        else {
            cf_free(state, y);
            cf_emit_set(state, r, y);
        }
    }
    if (state->pass == 3 && target_x)
        state->instr[target_x] = state->ip;
    // todo: use union function
    for (index i = 0; i < assigned_x->count; i++)
        insert(&state->assigned, item(assigned_x, i));

    if (state->pass == 3 && c <= 1 + state->args->count)
        delete(&state->scalars, state->scalars->count-1);
    return r;
}


// dest == 0 or dest == INSTR_LAST means allocate new temp;
// latter means it's going to be returned from the function

static instr_word cf_dest(struct cf_state* state, instr_word dest) {
    if (dest == 0 || dest == INSTR_LAST)
        return cf_temp(state);
    else
        return dest;
}


Value create_func(Value tree, Value args, struct cf_state* scope);

static Value func_close_flag;

static instr_word cf_recurse_call(struct cf_state* state,
                                 Value tree, instr_word dest) {
    // returns INSTR_LAST if code to return from the function has been emitted

    assert(IS_MIXED(tree) && tree->count > 1);
    Value verb = tree->mixed[0];

    // x:y x::y x[i]:y
    if ((verb->type == type_verb_prime || verb->type == type_verb) &&
            verb->verb == verb_null && tree->count == 3) {
        Value var = tree->mixed[1];
        if (!var->vector && var->type == type_name) {
        assign_var:;
            instr_word r = cf_name_write(state, var, verb->type == type_verb);
            instr_word x = cf_recurse(state, tree->mixed[2], r);
            cf_free(state, x);
            if (state->pass >= 2 &&
                    r >= 1 + state->args->count && r < 2*INSTR_PART)
                insert(&state->assigned, var);
            if (!r) { // global
                r = cf_dest(state, dest);
                cf_emit_4(state, verb_global_write,
                                 r, cf_literal(state, var), x);
            } else if (x != r)
                cf_emit_set(state, r, x);
            return r;
        } else if (IS_MIXED(var) && var->count && !var->mixed[0]->vector &&
                   var->mixed[0]->type == type_name) {
            if (var->count == 1 || var->count == 2 && IS_NULL(var->mixed[1])) {
                var = var->mixed[0];
                goto assign_var;
            }

            instr_word r = cf_name_read(state, var->mixed[0]), g = 0;
            instr_word x = cf_recurse(state, tree->mixed[2], 0);
            if (2 + (var->count-1) - 2 >= INSTR_PART/2)
                error(error_args);
            instr_word i[var->count-1];
            for (index j = var->count-1; j > 0; j--)
                if (IS_NULL(var->mixed[j])) {
                    i[j-1] = 3*INSTR_PART + state->literals->count;
                    state->use_null = 1;
                    // the call will not be partial, NULLs in the argument list
                    // will be handled by the special verb
                } else
                    i[j-1] = cf_recurse(state, var->mixed[j], 0);
            for (index j = 0; j < var->count-1; j++)
                cf_free(state, i[j]);
            cf_free(state, x);

            if (!r) { // global
                r = cf_dest(state, dest);
                g = cf_literal(state, var->mixed[0]);
                cf_emit_3(state, INSTR_PART + verb_global_read, r, g);
            }
            // must insert this literal before pass 3
            instr_word verb = cf_literal(state,
                (Value)&verbs[var->count == 2 ? verb_assign_item
                                              : verb_assign_element].literal);
            if (state->pass == 3) {
                // r : verb[r, x, i1, i2, ..., in]
                // error_args condition above is guarding this clause
                cf_emit_reserve(state, 5 + (var->count-1));
                assert(2 + (var->count-1) < 32);
                state->instr[state->ip++] =
                    2*INSTR_PART + (2 + (var->count-1) - 2);
                state->instr[state->ip++] = r;
                state->instr[state->ip++] = verb;
                state->instr[state->ip++] = r;
                state->instr[state->ip++] = x;
                for (index j = 0; j < var->count-1; j++)
                    state->instr[state->ip++] = i[j];
            }
            if (g)
                cf_emit_4(state, verb_global_write, r, g, r);
            return r;
        } else
            error(error_type);
    }

    // $[c;x;y]
    if (verb->type == type_verb && verb->verb == verb_cast &&
            tree->count >= 4 && tree->count % 2 == 0)
        return cf_recurse_cond(state, tree, dest, 1);

    // *x
    if (tree->count == 2 && verb->type == type_verb_prime) {
        instr_word x = cf_recurse(state, tree->mixed[1], 0);
        cf_free(state, x);
        instr_word r = cf_dest(state, dest);
        cf_emit_3(state, INSTR_PART + tree->mixed[0]->verb, r, x);
        return r;
    }

    // x+y
    if (tree->count == 3 && verb->type == type_verb &&
            !IS_NULL(tree->mixed[1]) && !IS_NULL(tree->mixed[2])) {
        instr_word y = cf_recurse(state, tree->mixed[2], 0);
        instr_word x = cf_recurse(state, tree->mixed[1], 0);
        cf_free(state, x); cf_free(state, y);
        instr_word r = cf_dest(state, dest);

        Verb v = tree->mixed[0]->verb;
        if (in(state->scalars, create_index(x)) &&
            in(state->scalars, create_index(y)))
            switch (v) {
            case verb_plus:  v = verb_scalar_plus;  break;
            case verb_minus: v = verb_scalar_minus; break;
            }
        cf_emit_4(state, v, r, x, y);
        return r;
    }

    // x+:y
    if (tree->count == 3 && verb->type == type_verb_prime) {
        Value var = tree->mixed[1];
        if (var->vector || var->type != type_name)
            error(error_type);
        instr_word r = cf_name_read(state, var), g = 0;
        instr_word x = cf_recurse(state, tree->mixed[2], 0);
        cf_free(state, x);
        if (!r) {
            r = cf_dest(state, dest);
            g = cf_literal(state, var);
            cf_emit_3(state, INSTR_PART + verb_global_read, r, g);
        }
        cf_emit_4(state, tree->mixed[0]->verb, r, r, x);
        if (g)
            cf_emit_4(state, verb_global_write, r, g, r);
        return r;
    }

    // [...;...;...]
    if (!verb->vector && verb->type == type_char && verb->_char == ';') {
        for (index i = 1; i < tree->count-1; i++)
            cf_free(state, cf_recurse(state, tree->mixed[i], 0));
        return cf_recurse(state, tree->mixed[tree->count-1], dest);
    }

    // {x}
    if (!verb->vector && verb->type == type_char &&
            verb->_char == '{' && tree->count == 3 &&
            tree->mixed[1]->vector && tree->mixed[1]->type == type_name) {
        if (state->pass == 2)
            return cf_literal(state, create_func(tree->mixed[2],
                tree->mixed[1]->count ? tree->mixed[1] : NULL, state));
        else if (state->pass == 3) {
            for (; state->literals->mixed[state->literal_func]->
                   type != type_func; state->literal_func++);
            index i = state->literal_func++;
            instr_word x = 3*INSTR_PART + i;
            if (state->literals->mixed[i]->func.upvalues == &func_close_flag) {
                instr_word r = cf_dest(state, dest);
                cf_emit_4(state, verb_init_closure, r, x,
                                 1 + state->args->count);
                return r;
            } else
                return x;
        } else
            return 0;
    }

    // :x
    if (!verb->vector && verb->type == type_char && verb->_char == ':' &&
            tree->count == 2) {
        instr_word r = cf_recurse(state, tree->mixed[1], INSTR_LAST);
        cf_free(state, r);
        if (r != INSTR_LAST)
            cf_emit_2(state, 3*INSTR_PART + 0, r);
        return INSTR_LAST;
    }

    // if[c;...] while[c;...]
    if (!verb->vector && verb->type == type_name &&
            (verb->_name == name_if || verb->_name == name_while)) {
        instr_word start = state->ip;
        instr_word c = cf_recurse(state, tree->mixed[1], 0);
        cf_free(state, c);
        cf_emit_3(state, 3*INSTR_PART + 2, 0, c);
        instr_word target = state->ip - 2;
        if (state->pass == 3 && c <= 1 + state->args->count)
            push(&state->scalars, create_index(c));

        for (index i = 2; i < tree->count; i++)
            cf_free(state, cf_recurse(state, tree->mixed[i], 0));
        if (verb->_name == name_while)
            cf_emit_2(state, 3*INSTR_PART + 1, start);
        if (state->pass == 3)
            state->instr[target] = state->ip;

        if (state->pass == 3 && c <= 1 + state->args->count)
            delete(&state->scalars, state->scalars->count-1);

        return cf_literal(state, (Value)&untyped_null);
    }

    // do[n;...]
    if (!verb->vector && verb->type == type_name && verb->_name == name_do) {
        instr_word x = cf_recurse(state, tree->mixed[1], 0);
        cf_free(state, x);
        instr_word c = cf_temp(state);
        cf_emit_3(state, INSTR_PART + verb_init_counter, c, x);
        if (state->pass == 3 && c <= 1 + state->args->count)
            push(&state->scalars, create_index(c));

        cf_emit_2(state, 3*INSTR_PART + 1, 0);
        instr_word start = state->ip;
        for (index i = 2; i < tree->count; i++)
            cf_free(state, cf_recurse(state, tree->mixed[i], 0));
        if (state->pass == 3)
            state->instr[start-1] = state->ip;
        cf_emit_3(state, 3*INSTR_PART + 3, start, c);
        cf_free(state, c);

        if (state->pass == 3 && c <= 1 + state->args->count)
            delete(&state->scalars, state->scalars->count-1);

        return cf_literal(state, (Value)&untyped_null);
    }

    // self[...] tail call
    if (state->pass == 3 && dest == INSTR_LAST && !verb->vector &&
            verb->type == type_name && verb->_name == name_self &&
            !state->closed_locals->count &&
            tree->count == state->args->count + 1) {
        for (index i = tree->count-1; i > 0; i--)
            if (tree->count != 2 && IS_NULL(tree->mixed[i]))
                goto self_skip;

        instr_word x[tree->count-1];
        for (index i = tree->count-1; i > 0; i--)
            x[i-1] = cf_recurse(state, tree->mixed[i], i == 1 ? 1 : 0);
        for (index i = 1; i < tree->count; i++) {
            cf_free(state, x[i-1]);
            if (x[i-1] != i)
                cf_emit_set(state, i, x[i-1]);
        }
        cf_emit_2(state, 3*INSTR_PART + 1, 0);
        return INSTR_LAST;
    }
self_skip:;

    // f[x;y;z]
    if (tree->count > 2 && (tree->count-1) - 2 >= INSTR_PART/2)
        error(error_args);
    instr_word x[tree->count];
    bool partial = 0;
    for (index i = tree->count-1; i >= 0; i--)
        if (tree->count != 2 && i && IS_NULL(tree->mixed[i])) {
            x[i] = 3*INSTR_PART + state->literals->count;
            state->use_null = 1;
            partial = 1;
        } else
            x[i] = cf_recurse(state, tree->mixed[i], 0);
    for (index i = 0; i < tree->count; i++)
        cf_free(state, x[i]);
    instr_word r = cf_dest(state, dest);
    if (state->pass == 3) {
        assert(tree->count >= 2);
        if (tree->count == 2)
            cf_emit_4(state, verb_at, r, x[0], x[1]);
        else {
            // error_args condition above is guarding this clause
            // r : x1[x2, x3, ..., xn]
            cf_emit_reserve(state, 3 + (tree->count-1));
            state->instr[state->ip++] = 2*INSTR_PART +
                (partial ? INSTR_PART/2 : 0) + ((tree->count-1) - 2);
            state->instr[state->ip++] = r;
            for (index i = 0; i < tree->count; i++)
                state->instr[state->ip++] = x[i];
        }
    }
    return r;
}


static instr_word cf_recurse(struct cf_state* state, Value tree,
                             instr_word dest) {
    if (IS_MIXED(tree))
        switch (tree->count) {
        case 0:
            return cf_literal(state, tree);
        case 1:
            return cf_literal(state, *tree->mixed);
        default: {
            Value constant = cf_transform(tree);
            if (constant != tree)
                return cf_recurse(state, constant, dest);
            return cf_recurse_call(state, tree, dest);
        }
        }
    else
        if (IS_NUMERIC(tree) || IS_CALLABLE(tree))
            return cf_literal(state, tree);
        else if (tree->type == type_name)
            if (tree->vector)
                return cf_recurse(state, weaken(tree), dest);
            else {
                if (state->scope && tree->_name == name_self)
                    return 0;
                instr_word r = cf_name_read(state, tree);
                if (!r) {
                    r = cf_dest(state, dest);
                    cf_emit_3(state, INSTR_PART + verb_global_read,
                                     r, cf_literal(state, tree));
                }
                return r;
            }
        else
            error(cons(error_compile, tree));
}


Value create_func(Value tree, Value args, struct cf_state* scope) {
    assert(!args || args->vector && args->type == type_name);

    struct cf_state state = {
        0, scope, alloc(sizeof *state.instr * 2, alloc_normal), 0,
        create_items(type_bool, 0),
        args ? (MValue)args : create_items(type_name, 0),
        create_items(type_name, 0), create_items(type_name, 0),
        create_items(type_name, 0), create_items(type_name, 0),
        create_items(type_index, 0), create_items(type_variant, 0), 0,
        0, 0, !args
    };

    if (state.args->count >= INSTR_PART - 2)
        error(error_args);

    state.pass = 1;
    cf_recurse(&state, tree, INSTR_LAST);
    if (state.auto_args && !state.args->count)
        push(&state.args, name_null);
    state.assigned = create_items(type_name, 0);

    state.pass = 2;
    cf_recurse(&state, tree, INSTR_LAST);
    state.assigned = create_items(type_name, 0);

    state.pass = 3;
    // copy args into closure at start
    for (index i = 0; i < state.args->count; i++) {
        index j;
        if (find_item_check(&j, state.closed_locals, item(state.args, i)))
            cf_emit_set(&state, INSTR_PART+j, 1+i);
    }
    // initialize possibly unitialized closure members at start
    for (index i = 0; i < state.closed_init->count; i++) {
        index j;
        if (find_item_check(&j, state.closed_locals,
                                item(state.closed_init, i)))
            cf_emit_set(&state, INSTR_PART+j,
                        cf_literal(&state, (Value)&untyped_null));
        else
            assert_failed("closed init is not subset of closed locals "
                          "during compilation");
    }
    instr_word r = cf_recurse(&state, tree, INSTR_LAST);
    if (r != INSTR_LAST)
        cf_emit_2(&state, 3*INSTR_PART + 0, r);
    cf_free(&state, r);
    if (in(state.temps, create_bool(1))) // todo: replace with max
        assert_failed("not all temps were freed during compilation");

    state.use_null = 1; // always put null on end to determine end of literals
    Value* literals =
        alloc(sizeof *literals * (state.literals->count + state.use_null),
              alloc_normal);
    assert(IS_MIXED(state.literals));
    memcpy(literals, state.literals->mixed,
           sizeof *literals * state.literals->count);
    if (state.use_null)
        literals[state.literals->count] = NULL;

    MValue func = create_item(type_func);
    func->func.code = code(state.args->count,
                           1 + state.args->count +
                             !!state.closed_locals->count +
                               state.free_locals->count +
                               state.temps->count,
                           state.closed_locals->count, state.instr, literals);
    func->func.upvalues = state.use_upvalues ? &func_close_flag : NULL;
    //disasm(func);
    return func;
}


static Value eval_tree(Value tree) {
    if (IS_NUMERIC(tree))
        return tree;
    if (IS_MIXED(tree) && tree->count == 1)
        return tree->mixed[0];

    Value func = create_func(tree, NULL, NULL);
    Value frame[func->func.code->frame];
    bzero(frame, sizeof frame);
    frame[0] = func;
    frame[1] = (Value)&untyped_null;
    Value r = run(frame); // VC: stack including function is accounted in run
    hold(r);
    collect();
    release(1);
    return r;
}


Value eval(Value tree) {
    if (tree->vector && tree->type == type_char)
        tree = parse(tree);
    return eval_tree(tree);
}


Value eval_source(Value source) {
    return eval_tree(parse_source(source));
}


#ifndef NDEBUG

static void disasm_reg(instr_word r, Value* literals, MValue* inner) {
    printf("%c%d", "scel"[r/INSTR_PART], r%INSTR_PART);
    if (r/INSTR_PART == 3) {
        putchar('=');
        Value v = literals[r%INSTR_PART];
        if (!v)
            printf("null");
        else if (v->type == type_func) {
            push(inner, v);
            printf("inner_%d", (*inner)->count);
        } else {
            v = repr(v);
            printf("%.*s", v->count, v->chars);
        }
    }
}


#define MAX(x, y) ((x) > (y) ? (x) : (y))

static void disasm_indented(Value value, int indent) {
    if (value->type != type_func)
        error(error_type);
    const Func const* func = &value->func;
    const instr_word *const instr = func->code->instr;
    MValue inner = create_items(type_variant, 0);

    #define DISASM_REG(x) disasm_reg(x, func->code->literals, &inner);

    for (unsigned ip = 0, end = 0; ip <= end;) {
        printf("%*d: ", indent + 4, ip);
        switch (instr[ip] / INSTR_PART) {
        case 0: {
            DISASM_REG(instr[ip+1]); printf(" : ");
            DISASM_REG(instr[ip+2]); putchar(' ');
            int verb = instr[ip];
            if (verb < sizeof verbs / sizeof *verbs && verbs[verb].name)
                putchar(verbs[verb].name);
            else
                switch (verb) {
                case verb_global_write: printf("global_write"); break;
                case verb_init_closure: printf("init_closure"); break;
                case verb_scalar_plus:  printf("+."); break;
                case verb_scalar_minus: printf("-."); break;
                default:                printf("(%d)", verb);
                }
            putchar(' '); DISASM_REG(instr[ip+3]);
            ip += 4;
            end = MAX(end, ip);
            break;
        }
        case 1: {
            DISASM_REG(instr[ip+1]); printf(" : ");
            int verb = instr[ip] % INSTR_PART;
            if (verb < sizeof verbs / sizeof *verbs && verbs[verb].name)
                printf("%c:", verbs[verb].name);
            else
                switch (verb) {
                case verb_global_read:  printf("global_read"); break;
                case verb_init_counter: printf("init_counter"); break;
                default:                printf("(%d)", verb);
                }
            putchar(' '); DISASM_REG(instr[ip+2]);
            ip += 3;
            end = MAX(end, ip);
            break;
        }
        case 2: {
            int n = instr[ip] % (INSTR_PART/2) + 2;
            for (int i = 1; i < n+3; i++) {
                DISASM_REG(instr[ip+i]);
                printf(i == 1 ? " : " : i == 2 ? "[" : i == n+2 ? "]" : "; ");
            }
            ip += 3 + n;
            end = MAX(end, ip);
            break;
        }
        default:
            switch (instr[ip] % INSTR_PART) {
            case 0:
                printf("ret "); DISASM_REG(instr[ip+1]);
                ip += 2;
                break;
            case 1:
                printf("jmp %d", instr[ip+1]);
                end = MAX(end, instr[ip+1]);
                ip += 2;
                break;
            case 2: {
                printf("jz "); DISASM_REG(instr[ip+2]);
                printf(" %d", instr[ip+1]);
                end = MAX(end, instr[ip+1]);
                ip += 3;
                end = MAX(end, ip);
                break;
            }
            case 3:
                printf("loop "); DISASM_REG(instr[ip+2]);
                printf(" %d", instr[ip+1]);
                end = MAX(end, instr[ip+1]);
                ip += 3;
                end = MAX(end, ip);
                break;
            default:
                assert_failed("unknown instruction");
            }
        }
        putchar('\n');
    }

    for (index i = 0; i < inner->count; i++) {
        putchar('\n');
        disasm_indented(item(inner, i), indent + 4);
    }
}


Value disasm(Value value) {
    disasm_indented(value, 0);
    return (Value)&untyped_null;
}

#else /* NDEBUG */

Value disasm(Value value) {
    return (Value)&untyped_null;
}

#endif /* NDEBUG */
