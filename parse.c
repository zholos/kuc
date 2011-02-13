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

#include "parse.h"

#include "adverb.h"
#include "error.h"
#include "func.h"
#include "verb.h"

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#define index index_hide /* index() should be in string.h anyway */
#include <string.h>
#undef index


struct parse_state {
    const char* start, *end;
    const char* s;
    Value token; // char for punctuation, names, literals as single weak lists
    const char* token_start;
    index line; const char* line_start;
    bool comments_allowed;
};

#define AVAIL(n) (state->s + (n-1) < state->end)
#define NEXT(c) (*state->s == (c))
#define AFTER(c) (state->s[1] == (c))


#define MIN(x, y) ((x) < (y) ? (x) : (y))

static void __attribute__ ((noreturn)) parse_error(struct parse_state* state,
                                                   Value x) {
    ptrdiff_t c =
        (state->token_start ? state->token_start : state->s) - state->start;
    error(triplet(error_parse, create_index(MIN(c, index_max)), x));
}


static void skip_space(struct parse_state* state) {
    for (;;) {
        const char* base = state->s;
        for (; AVAIL(1) && isspace(*state->s) && *state->s != '\n'; state->s++);
        if (state->comments_allowed &&
                (state->s != base || state->s == state->line_start) &&
                AVAIL(1) && *state->s == '#')
            for (; AVAIL(1) && *state->s != '\n'; state->s++);
        if (AVAIL(1) && NEXT('\n')) {
            state->line++;
            state->line_start = ++state->s;
        } else
            break;
    }
}


#define LEX_INTEGER(vtype)                                                    \
static vtype##_type lex_##vtype(struct parse_state* state) {                  \
    vtype##_type n = 0;                                                       \
    assert(AVAIL(1) && (isdigit(*state->s) || NEXT('-') &&                    \
           AVAIL(2) &&  isdigit( state->s[1])));                              \
    /* here state->s is "-?[0-9]..." */                                       \
    bool negative = 0;                                                        \
    if (negative = NEXT('-'))                                                 \
        state->s++;                                                           \
    if (NEXT('0') && AVAIL(2) && (!negative && AFTER('N') || AFTER('W'))) {   \
        n = AFTER('N') ? vtype##_null : negative ? vtype##_min : vtype##_max; \
        state->s += 2;                                                        \
    } else                                                                    \
        for (; AVAIL(1) && isdigit(*state->s); state->s++) {                  \
            int digit = digittoint(*state->s);                                \
            if (negative ? n < (vtype##_min + digit) / 10                     \
                         : n > (vtype##_max - digit) / 10)                    \
                parse_error(state, error_number);                             \
            n = n * 10;                                                       \
            n = negative ? n - digit : n + digit;                             \
        }                                                                     \
    return n;                                                                 \
}

LEX_INTEGER(int)
LEX_INTEGER(long)


static float_type lex_float(struct parse_state* state) {
    assert(AVAIL(1));
    if (NEXT('0') && AVAIL(2) && (AFTER('n') || AFTER('w'))) {
        float_type r = AFTER('n') ? float_null : float_max;
        state->s += 2;
        return r;
    } else if (NEXT('-') && AVAIL(3) && AFTER('0') && state->s[2] == 'w') {
        state->s += 3;
        return float_min;
    } else {
        bool negative = NEXT('-');
        if (negative)
            state->s++;
        float_type x = 0;
        while (AVAIL(1) && isdigit(*state->s))
            x = x * 10 + digittoint(*state->s++);
        if (AVAIL(1) && NEXT('.')) {
            state->s++;
            float_type f = 0, p = 1;
            for (; AVAIL(1) && isdigit(*state->s); p *= 10)
                f = f * 10 + digittoint(*state->s++);
            x += f / p;
        }
        if (AVAIL(1) && NEXT('e')) {
            state->s++;
            bool exp_negative = AVAIL(1) && NEXT('-');
            if (exp_negative)
                state->s++;
            float_type e = 0;
            while (AVAIL(1) && isdigit(*state->s))
                e = e * 10 + digittoint(*state->s++);
            // note: assuming that float_type is double
            x *= pow(10, exp_negative ? -e : e);
        }
        return negative ? -x : x;
    }
}


static bool lookahead_number(const char* s, const char* end,
                             bool accept_minus) {
    if (s < end) {
        if (isdigit(*s) || s + 1 < end && *s == '.' && isdigit(s[1]))
            return 1;
        if (accept_minus && s + 1 < end && *s == '-')
            return lookahead_number(s + 1, end, 0);
    }
    return 0;
}


static int bool_digit(char c) {
    int d = digittoint(c);
    return d <= 1 ? d : d == 8 ? -1 : 2;
}


static Value lex_numbers(struct parse_state* state) {
    bool boolean = 1, integer = 1, floating = 1;
    index items = 1;
    const char* base = state->s;
    for (;;) {
        assert(lookahead_number(state->s, state->end, 1));
        // here state->s is "-?.?[0-9]..."
        bool negative;
        if (negative = NEXT('-')) {
            boolean = 0;
            state->s++;
        }
        if (NEXT('0') && AVAIL(2) && ((AFTER('N') || AFTER('n')) && !negative ||
                                      (AFTER('W') || AFTER('w')))) {
            bool this_floating = AFTER('n') || AFTER('w');
            if (this_floating ? !floating : !integer) {
                state->s++;
                parse_error(state, error_number);
            }
            if (this_floating)
                integer = 0;
            else
                floating = 0;
            boolean = 0;
            state->s += 2;
        } else {
            bool allow_decimal = floating;
            for (; AVAIL(1) && (isdigit(*state->s) || NEXT('.')); state->s++) {
                if (NEXT('.')) {
                    if (allow_decimal)
                        allow_decimal = integer = boolean = 0;
                    else
                        parse_error(state, error_number);
                } else
                    boolean = boolean && bool_digit(*state->s) != 2;
            }
            if (floating && AVAIL(1) && NEXT('e')) {
                integer = boolean = 0;
                state->s++;
                if (NEXT('-'))
                    state->s++;
                if (!(AVAIL(1) && isdigit(*state->s)))
                    parse_error(state, error_number);
                for (; AVAIL(1) && isdigit(*state->s); state->s++);
            }
        }

        const char* rewind = state->s;
        skip_space(state);
        if (rewind != state->s && lookahead_number(state->s, state->end, 1)) {
            if (items >= index_max - 1)
                parse_error(state, error_number);
            items++;
        } else {
            state->s = rewind;
            break;
        }
    }

    if (AVAIL(1) && isalnum(*state->s)) {
        if (AVAIL(2) && isalnum(state->s[1]))
            goto bad_suffix;
        else if (NEXT('b')) {
            if (!boolean || items > 1)
                parse_error(state, error_number);
            if (state->s == base + 1) {
                state->s++;
                return create_bool(bool_digit(*base));
            } else {
                if (state->s - base >= index_max) {
                    // this sort of error isn't possible if source is passed
                    // through a char vector, but can happen for an mmap'd file
                    state->s = base + index_max;
                    parse_error(state, error_number);
                }
                index n = state->s - base;
                state->s++;
                MValue b = create_items(type_bool, n);
                for (index i = 0; i < n; i++)
                    b->bools[i] = bool_digit(*base++);
                return b;
            }
        } else if (NEXT('j')) {
            if (!integer)
                parse_error(state, error_number);
            state->s = base;
            Value numbers;
            if (items > 1) {
                MValue r = create_items(type_long, items);
                for (index i = 0; i < items; i++) {
                    if (i)
                        skip_space(state);
                    r->longs[i] = lex_long(state);
                }
                numbers = r;
            } else
                numbers = create_long(lex_long(state));
            assert(AVAIL(1) && NEXT('j'));
            state->s++;
            return numbers;
        } else
        bad_suffix:
            parse_error(state, error_number);
    } else {
        state->s = base;
        if (integer)
            if (items > 1) {
                MValue numbers = create_items(type_int, items);
                for (index i = 0; i < items; i++) {
                    if (i)
                        skip_space(state);
                    numbers->ints[i] = lex_int(state);
                }
                return numbers;
            } else
                return create_int(lex_int(state));
        else
            if (items > 1) {
                MValue numbers = create_items(type_float, items);
                for (index i = 0; i < items; i++) {
                    if (i)
                        skip_space(state);
                    numbers->floats[i] = lex_float(state);
                }
                return numbers;
            } else
                return create_float(lex_float(state));
    }
}


static byte_type byte_digits(const char s[2]) {
    return digittoint(s[0]) * 16 + digittoint(s[1]);
}


static Value lex_bytes(struct parse_state* state) {
    assert(AVAIL(1) && NEXT('0') && AVAIL(2) && AFTER('x'));
    const char* base = state->s += 2;
    for (; AVAIL(1) && isxdigit(*state->s); state->s++);
    if (AVAIL(1) && isalnum(*state->s))
        parse_error(state, error_number);

    if ((state->s - base) % 2)
        base--; // digittoint will return 0 for 'x' from prefix
    index n = (state->s - base) / 2;
    if (n == 1)
        return create_byte(byte_digits(base));
    else {
        MValue b = create_items(type_byte, n);
        for (index i = 0; i < n; i++, base += 2)
            b->bytes[i] = byte_digits(base);
        return b;
    }
}


static bool is_name_char(char c) {
    return isalnum(c);
}

static bool is_filename_char(char c, bool filename) {
    if (filename && (c == '/' || c == '.'))
        return 1;
    return is_name_char(c);
}

static Value lex_name(struct parse_state* state) {
    // name may contain internal underscores;
    // if it begins with a colon (which is only possible when called from
    // lex_names()) it may also contain slashes and dots
    const char* base = state->s;
    bool filename = AVAIL(1) && NEXT(':');
    if (filename)
        state->s++;
    for (;;) {
        for (; AVAIL(1) && is_filename_char(*state->s, filename); state->s++);
        const char* rewind = state->s;
        for (; AVAIL(1) && NEXT('_'); state->s++);
        if (!(rewind != state->s &&
                AVAIL(1) && is_filename_char(*state->s, filename))) {
            state->s = rewind;
            break;
        }
    }

    if (state->s - base >= index_max) {
        state->s = base + index_max;
        parse_error(state, error_name);
    }
    // note: source was obtained from char vector so length can't overflow
    return create_name(base, state->s - base);
}


static Value lex_names(struct parse_state* state) {
    assert(AVAIL(1) && NEXT('`'));
    state->s++;
    Value r = lex_name(state);

    if (AVAIL(1) && NEXT('`')) {
        MValue v = create_items(type_name, 1);
        v->names[0] = r->_name;
        while (AVAIL(1) && NEXT('`')) {
            state->s++;
            push(&v, lex_name(state));
        }
        r = v;
    }
    return box(r);
}


static bool is_octal_digit(char c) {
    return isdigit(c) && digittoint(c) < 8;
}


static Value lex_string(struct parse_state* state) {
    assert(AVAIL(1) && NEXT('"'));
    state->s++;
    MValue r = NULL; // initialization not really needed
    const char* rewind = state->s;
    for (char* c = NULL;;) // two passes: scan and create
        // note: source was obtained from char vector so length can't overflow
        for (index i = 0;; i++) {
            if (!AVAIL(1) || i == index_max || iscntrl(*state->s))
                parse_error(state, error_string);
            else if (NEXT('\\')) {
                state->s++;
                if (AVAIL(1) && (NEXT('\\') || NEXT('"'))) {
                    if (c)
                        c[i] = *state->s;
                    state->s++;
                } else if (AVAIL(1) && NEXT('n')) {
                    if (c)
                        c[i] = '\n';
                    state->s++;
                } else if (AVAIL(1) && is_octal_digit(*state->s)) {
                    int o = digittoint(*state->s++);
                    if (AVAIL(1) && is_octal_digit(*state->s)) {
                        o = o * 8 + digittoint(*state->s++);
                        if (o * 8 < 256 &&
                                AVAIL(1) && is_octal_digit(*state->s))
                            o = o * 8 + digittoint(*state->s++);
                    }
                    if (c)
                        c[i] = (unsigned char)o;
                } else
                    parse_error(state, error_string);
            } else if (NEXT('"')) {
                state->s++;
                if (c)
                    return box(r);
                else {
                    if (i == 1) {
                        r = create_item(type_char);
                        c = &r->_char;
                    } else {
                        r = create_items(type_char, i);
                        c = r->chars;
                    }
                    state->s = rewind;
                    break;
                }
            } else {
                if (c)
                    c[i] = *state->s;
                state->s++;
            }
        }
}


static void lex_next(struct parse_state* state) {
    state->token_start = NULL; // while lexing show errors at character location

    const char* base = state->s;
    skip_space(state);
    const char* token_start = state->s;

    bool minus_is_verb = base == state->s &&
                         state->token && state->token->type != type_char;
    // special rule: '-' is a verb directly after punctuation

    if (!AVAIL(1))
        state->token = NULL;
    else if (NEXT('0') && AVAIL(2) && AFTER('x'))
        state->token = lex_bytes(state);
    else if (lookahead_number(state->s, state->end, !minus_is_verb))
        state->token = lex_numbers(state);
    else if (is_name_char(*state->s))
        state->token = lex_name(state);
    else if (NEXT('`'))
        state->token = lex_names(state);
    else if (NEXT('"'))
        state->token = lex_string(state);
    else if (ispunct(*state->s))
        // note: verbs and adverbs depend on parsing context, so only produce
        // punctuation characters in lexer
        state->token = create_char(*state->s++);
    else
        parse_error(state, error_unknown);

    state->token_start = token_start; // while parsing show errors at token
}


static char next_punct(struct parse_state* state) {
    if (state->token &&
            !state->token->vector && state->token->type == type_char)
        return state->token->_char;
    return 0;
}


static void parse_punct(struct parse_state* state, char punct) {
    if (next_punct(state) == punct)
        lex_next(state);
    else
        parse_error(state, cons(error_expected, create_char(punct)));
}


static bool accept_punct(struct parse_state* state, char punct) {
    if (next_punct(state) == punct) {
        lex_next(state);
        return 1;
    } else
        return 0;
}


static Value simplify_seq(Value seq) {
    return seq->count == 1 ? (Value)&untyped_null  :
           seq->count == 2 ? seq->mixed[1] : seq;
}


static Value parse_expr(struct parse_state* state);
static Value parse_seq(struct parse_state* state, MValue, char);

static Value accept_term(struct parse_state* state) {
    if (!state->token)
        return NULL;

    if (!next_punct(state)) {
        Value literal = state->token;
        lex_next(state);
        return literal;
    }

    if (accept_punct(state, '(')) {
        if (accept_punct(state, ')'))
            return (Value)&empty;
        Value first = parse_expr(state);
        if (accept_punct(state, ';'))
            return parse_seq(state,
                (MValue)cons((Value)&verbs[verb_list].literal, first), ')');
        else {
            parse_punct(state, ')');
            return first;
        }
    }

    if (accept_punct(state, '{')) {
        MValue names = create_items(type_name, 0);
        if (accept_punct(state, '[')) {
            for (;;) {
                if (state->token && !state->token->vector &&
                                    state->token->type == type_name) {
                    push(&names, state->token);
                    lex_next(state);
                } else
                    push(&names, name_null);
                if (accept_punct(state, ']'))
                    break;
                else
                    parse_punct(state, ';');
            }
        }
        return triplet(create_char('{'), names, simplify_seq(
            parse_seq(state, (MValue)box(create_char(';')), '}')));
    }
    return NULL;
}


static Value accept_verb(struct parse_state* state) {
    char punct = next_punct(state);
    if (!punct)
        return NULL;
    for (int i = 0; i <= verb_named_last; i++)
        if (punct == verbs[i].name) {
            lex_next(state);
            // fixme: only accept prime if unary function exists
            if (accept_punct(state, ':'))
                return (Value)&verbs[i].literal_prime;
            return (Value)&verbs[i].literal;
        }
    return NULL;
}


static Value accept_adverb(struct parse_state* state) {
    char punct = next_punct(state);
    if (!punct)
        return NULL;
    int single = -1, two = -1;
    for (int i = 0; i <= adverb_named_last; i++)
        if (punct == adverbs[i].name)
            if (adverbs[i].colon)
                two = i;
            else
                single = i;

    // note: since we only have one character of lookahead, it is assumed that
    // every two-character adverb has a single-character counterpart
    if (single >= 0) {
        lex_next(state);
        if (two >= 0 && accept_punct(state, ':'))
            return (Value)&adverbs[two].literal;
        return (Value)&adverbs[single].literal;
    }
    return NULL;
}


static Value accept_node(struct parse_state* state, bool* op) {
    // returns NULL if empty
    Value r;
    if (r = accept_verb(state))
        *op = 1;
    else if (r = accept_term(state))
        ;
    else
        return NULL;

    for (;;) {
        Value adverb;
        if (adverb = accept_adverb(state))
            r = cons(adverb, r), *op = 1;
        else if (accept_punct(state, '['))
            r = parse_seq(state, (MValue)box(r), ']'), *op = 0;
        else
            break;
    }
    return r;
}


static Value unary_op(Value op) {
    if (op->type == type_verb)
        return (Value)&verbs[op->verb].literal_prime;
    if (IS_MIXED(op) && op->count == 2 &&
            op->mixed[0]->type == type_clause &&
            op->mixed[0]->clause.adverb == adverb_each) {
        Value op1 = unary_op(op->mixed[1]);
        return op1 == op->mixed[1] ? op : cons(op->mixed[0], op1);
    }
    return op;
}


static Value parse_expr_tail(struct parse_state* state,
                             Value left, bool left_op, bool* op) {
    // *op must be initialized to 0
    // returns NULL if empty (providing left guarantees non-empty)
    if (!left)
        left = accept_node(state, &left_op);
    if (!left)
        return NULL;

    if (left_op) {
        bool right_op = 0;
        Value right = parse_expr_tail(state, NULL, 0, &right_op);
        if (right) {
            left = unary_op(left);
            if (right_op)
                return *op = 1, triplet((Value)&verbs[verb_accent].literal,
                                        left, right);
            else
                return cons(left, right);
        } else
            return *op = 1, left;
    } else {
        bool verb_op = 0;
        Value verb = accept_node(state, &verb_op);
        if (verb)
            if (verb_op) {
                bool assign = (verb->type == type_verb ||
                                verb->type == type_verb_prime) &&
                                verb->verb == verb_null;
                bool right_op = 0;
                Value right = parse_expr_tail(state, NULL, 0, &right_op);
                if (right)
                    if (right_op && !assign)
                        return *op = 1,
                            triplet((Value)&verbs[verb_accent].literal,
                                    cons(verb, left), right);
                    else
                        return triplet(verb, left, right);
                else
                    return *op = 1, cons(verb, left);
            } else {
                bool right_op = 0;
                Value right = parse_expr_tail(state, verb, verb_op, &right_op);
                if (right_op)
                    return *op = 1, triplet((Value)&verbs[verb_accent].literal,
                                            left, right);
                else
                    return cons(left, right);
            }
        else
            return left;
    }
}


static Value parse_expr(struct parse_state* state) {
    if (accept_punct(state, '['))
        return parse_seq(state, (MValue)box(create_char(';')), ']');

    // follow parse_exrp_tail but handle : specially at start
    bool left_op = 0, op = 0, returning = 0;
    Value left = accept_node(state, &left_op), tail;
    if (left && left->type == type_verb && left->verb == verb_null) {
        tail = parse_expr_tail(state, NULL, 0, &op);
        if (tail)
            returning = 1;
        else {
            tail = left;
            op = left_op;
        }
    } else
        tail = parse_expr_tail(state, left, left_op, &op);

    if (!tail)
        tail = (Value)&untyped_null;
    else if (op && !tail->vector)
        tail = box(tail);

    return returning ? cons(create_char(':'), tail) : tail;
}


static Value parse_seq(struct parse_state* state, MValue list, char close) {
    // list will be changed
    for (;;) {
        push(&list, parse_expr(state));
        if (!accept_punct(state, ';')) {
            if (close)
                parse_punct(state, close);
            return list;
        }
    }
}


static void init_state(struct parse_state* state, Value source,
                                                  bool comments_allowed) {
    if (!source->vector || source->type != type_char)
        error(error_type);

    const char* s = source->chars;
    struct parse_state v = { s, s + source->count, s, NULL, NULL, 1, s,
                             comments_allowed };
    *state = v;
    lex_next(state);
}


Value lex(Value source) {
    struct parse_state state;
    init_state(&state, source, 0);

    MValue r = create_items(type_variant, 0);
    for (; state.token; lex_next(&state))
        push(&r, state.token);
    return r;
}


Value parse_base(Value source, bool comments_allowed) {
    struct parse_state state;
    init_state(&state, source, comments_allowed);

    Value seq = parse_seq(&state, (MValue)box(create_char(';')), 0);
    if (state.token)
        parse_error(&state, error_parse);
    return simplify_seq(seq);
}


Value parse(Value source) {
    return parse_base(source, 0);
}


Value parse_source(Value source) {
    return parse_base(source, 1);
}
