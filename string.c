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

#include "string.h"

#include "adverb.h"
#include "func.h"
#include "math.h"
#include "sys.h"
#include "verb.h"

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdio.h>
#include <stdint.h>

#define index index_hide /* index() should be in string.h anyway */
#include <string.h>
#undef index


static char inttodigit(int x) {
    assert(x < 16);
    return x < 10 ? '0' + x : "abcdef"[x-10];
}


static char booltodigit(bool_type x) {
    return x < 0 ? '8' : x > 0 ? '1' : '0';
}


#define ABS(x) ((x) < 0 ? -(x) : (x))
#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define MAX(x, y) ((x) > (y) ? (x) : (y))

struct number_case {
    long_type v;
    int len;
    char s[3];
};

static index repr_number_len(const struct number_case* nc, long_type x) {
    for (; nc->len; nc++)
        if (x == nc->v)
            return nc->len;

    int digits = x < 0; x = ABS(x);
    for (long_type v = x; v; v /= 10)
        digits++;
    return digits;
}


static char* repr_number_render(const struct number_case* nc,
                                char* t, long_type x, index len) {
    for (; nc->len; nc++)
        if (x == nc->v) {
            memcpy(t, nc->s, nc->len);
            return t + nc->len;
        }

    bool negative = x < 0; x = ABS(x);
    if (len < 0) {
        len = negative;
        for (long_type v = x; v; v /= 10)
            len++;
    }

    char* s = t += len;
    for (; x; x /= 10)
        *--s = inttodigit(x % 10);
    if (negative)
        *--s = '-';
    return t;
}


const struct number_case number_int[] = {
    { 0,        1,  "0"  }, 
    { int_null, 2,  "0N" },
    { int_min,  3, "-0W" },
    { int_max,  2,  "0W" },
    {}
};


const struct number_case number_long[] = {
    { 0,         1,  "0"  },
    { long_null, 2,  "0N" },
    { long_min,  3, "-0W" },
    { long_max,  2,  "0W" },
    {}
};


static Value repr_int(int x) {
    MValue r = create_items(type_char, repr_number_len(number_int, x));
    repr_number_render(number_int, r->chars, x, r->count);
    return r;
}


static Value repr_long(long_type x) {
    index len = repr_number_len(number_long, x);
    MValue r = create_items(type_char, len + 1);
    *repr_number_render(number_long, r->chars, x, len) = 'j';
    return r;
}


#define PRECISION 7
#define PRECISION10 10000000l
// long used for mantissa below fits up to 10^9

static index repr_float_len(float_type x) {
    // follows repr_float_render below

    switch (fpclassify(x)) {
    case FP_ZERO:     return 2;           // 0.
    case FP_NAN:      return 2;           // 0n
    case FP_INFINITE: return (x < 0) + 2; // [-]0w
    }

    bool negative = x < 0; x = ABS(x);

    // note: assuming below that float_type is double
    int exponent = lround(floor(log10(x)));
    long mantissa = lround(x * pow(10, PRECISION - exponent - 1));
    if (mantissa >= PRECISION10) {
        exponent++;
        mantissa /= 10;
    }

    index trim = 0;
    for (long v = mantissa; trim < PRECISION && v % 10 == 0; v /= 10)
        trim++;

    if (exponent <= -PRECISION || exponent >= PRECISION) {
        index exp_digits = 0;
        for (int v = ABS(exponent); v; v /= 10) // exponent != 0 here
            exp_digits++;
        return negative + PRECISION - trim + 2 + (exponent < 0) + exp_digits;
    } else {
        trim = MIN(trim, PRECISION - exponent - 1);
        return negative + MAX(0, -exponent) + PRECISION - trim + 1;
    }
}


static char* repr_float_render(char* t, float_type x) {
    switch (fpclassify(x)) {
    case FP_ZERO:     memcpy(t, "0.", 2); return t + 2;
    case FP_NAN:      memcpy(t, "0n", 2); return t + 2;
    case FP_INFINITE: if (x < 0) *t++ = '-'; memcpy(t, "0w", 2); return t + 2;
    }

    if (x < 0)
        *t++ = '-';
    x = ABS(x);

    // note: assuming below that float_type is double
    int exponent = lround(floor(log10(x)));
    long mantissa = lround(x * pow(10, PRECISION - exponent - 1));
    if (mantissa >= PRECISION10) {
        exponent++;
        mantissa /= 10;
    }

    index trim = 0;
    for (; trim < PRECISION && mantissa % 10 == 0; mantissa /= 10)
        trim++;

    if (exponent <= -PRECISION || exponent >= PRECISION) {
        for (index i = trim; i < PRECISION; i++, mantissa /= 10)
            t[PRECISION - i - (PRECISION - i <= 1)] = inttodigit(mantissa % 10);
        t[1] = '.';
        t += PRECISION - trim + 1;
        *t++ = 'e';

        if (exponent < 0) {
            *t++ = '-';
            exponent = -exponent;
        }
        index exp_digits = 0;
        for (int v = exponent; v; v /= 10) // exponent > 0 here
            exp_digits++;
        for (index i = 0; i < exp_digits; i++, exponent /= 10)
            t[exp_digits - i - 1] = inttodigit(exponent % 10);
        t += exp_digits;
    } else {
        if (exponent < 0) {
            memset(t, '0', -exponent + 1);
            t += -exponent;
        }
        for (; trim >= PRECISION - exponent; trim--)
            mantissa *= 10;
        for (index i = trim; i < PRECISION; i++, mantissa /= 10)
            t[PRECISION - i - (PRECISION - i <= exponent + 1)] =
                inttodigit(mantissa % 10);
        t[exponent + 1] = '.';
        t += PRECISION - trim + 1;
    }
    return t;
}


static Value repr_float(float_type x) {
    MValue r = create_items(type_char, repr_float_len(x));
    repr_float_render(r->chars, x);
    return r;
}


static MValue string_bools(const bool_type* b, index n, index dots) {
    MValue r = create_items(type_char, add_length(n, dots + 1));
    char* t = r->chars;
    for (index i = 0; i < n; i++)
        *t++ = booltodigit(b[i]);
    memset(t, '.', dots); t += dots;
    *t = 'b';
    return r;
}


static MValue string_bytes(const byte_type* b, index n, index dots) {
    MValue r = create_items(type_char, add_length(add_length(n, n), dots + 2));
    char* t = r->chars;
    *t++ = '0', *t++ = 'x';
    for (index i = 0; i < n; i++) {
        *t++ = inttodigit(b[i] / 16 % 16);
        *t++ = inttodigit(b[i] % 16);
    }
    memset(t, '.', dots);
    return r;
}


#define DOTS 3

#define STRING_VECTOR(vtype, size, render, prefix, infix, suffix)              \
static MValue string_##vtype##s(const vtype##_type* v, index n, index width) { \
    index dots = 0;                                                            \
    index chars = !!prefix + !!suffix, keep_chars = chars;                     \
    index m = n, keep_i = 0;                                                   \
    for (index i = 0; i < n; i++) {                                            \
        index len;                                                             \
        size                                                                   \
        if (width < 0) {                                                       \
            chars = add_length(chars, len);                                    \
            if (infix && i + 1 < n)                                            \
                chars = add_length(chars, 1);                                  \
        } else {                                                               \
            if (chars > width - (infix && i + 1 < n) - len) {                  \
                chars = keep_chars;                                            \
                m     = keep_i;                                                \
                dots = DOTS;                                                   \
                break;                                                         \
            }                                                                  \
            chars += (infix && i + 1 < n) + len;                               \
            if (chars <= width - DOTS) {                                       \
                keep_chars = chars;                                            \
                keep_i     = i + 1;                                            \
            }                                                                  \
        }                                                                      \
    }                                                                          \
                                                                               \
    MValue r = create_items(type_char, chars + dots);                          \
    char* t = r->chars;                                                        \
    if (prefix)                                                                \
        *t++ = prefix;                                                         \
    for (index i = 0; i < m; i++) {                                            \
        render                                                                 \
        if (infix && i + 1 < n)                                                \
            *t++ = infix;                                                      \
    }                                                                          \
    memset(t, '.', dots); t += dots;                                           \
    if (suffix)                                                                \
        *t++ = suffix;                                                         \
    assert(t == r->chars + r->count);                                          \
    return r;                                                                  \
}


#define STRING_INT_LEN \
    len = repr_number_len(number_int, v[i]);

#define STRING_INT_RENDER \
    t = repr_number_render(number_int, t, v[i], -1);

STRING_VECTOR(int,  STRING_INT_LEN, STRING_INT_RENDER, 0, ' ', 0)


#define STRING_LONG_LEN \
    len = repr_number_len(number_long, v[i]);

#define STRING_LONG_RENDER \
    t = repr_number_render(number_long, t, v[i], -1);

STRING_VECTOR(long, STRING_LONG_LEN, STRING_LONG_RENDER, 0, ' ', 'j')


#define STRING_FLOAT_LEN \
    len = repr_float_len(v[i]);

#define STRING_FLOAT_RENDER \
    t = repr_float_render(t, v[i]);

STRING_VECTOR(float, STRING_FLOAT_LEN, STRING_FLOAT_RENDER, 0, ' ', 0)


static bool is_octal_digit(char c) {
    return isdigit(c) && c < '8';
}

#define STRING_CHAR_LEN                              \
    if (v[i] == '\\' || v[i] == '"' || v[i] == '\n') \
        len = 2;                                     \
    else if (isprint(v[i]))                          \
        len = 1;                                     \
    else                                             \
        len = i + 1 < n && is_octal_digit(v[i+1]) || \
                (unsigned char)v[i] >= 8 * 8 ? 4 :   \
                (unsigned char)v[i] >= 8 ? 3 : 2;

#define STRING_CHAR_RENDER                                        \
    if (v[i] == '\\' || v[i] == '"') {                            \
        *t++ = '\\';                                              \
        *t++ = v[i];                                              \
    } else if (v[i] == '\n') {                                    \
        *t++ = '\\';                                              \
        *t++ = 'n';                                               \
    } else if (isprint(v[i]))                                     \
        *t++ = v[i];                                              \
    else {                                                        \
        *t++ = '\\';                                              \
        bool next_octal = i + 1 < n && is_octal_digit(v[i+1]);    \
        if (next_octal || (unsigned char)v[i] >= 8 * 8)           \
            *t++ = inttodigit((unsigned char)v[i] / (8 * 8) % 8); \
        if (next_octal || (unsigned char)v[i] >= 8)               \
            *t++ = inttodigit((unsigned char)v[i] / 8 % 8);       \
        *t++ = inttodigit((unsigned char)v[i] % 8);               \
    }

STRING_VECTOR(char, STRING_CHAR_LEN, STRING_CHAR_RENDER, '"', 0, '"')


#define STRING_NAME_LEN \
    len = strlen(v[i]);

#define STRING_NAME_RENDER {   \
    size_t len = strlen(v[i]); \
    memcpy(t, v[i], len);      \
    t += len;                  \
}

STRING_VECTOR(name, STRING_NAME_LEN, STRING_NAME_RENDER, '`', '`', 0)


static MValue string_vector(Value x, index width) {
    // must return MValue, because it's used as line of cell
    assert(x->vector);

    if (!x->count)
        return create_string("()", 2);

    switch (x->type) {
    case type_bool: {
        index dots = (x->count > width - 1) * DOTS;
        return string_bools(x->bools,
                            MAX(0, MIN(x->count, width - dots - 1)), dots);
    }
    case type_byte: {
        index dots = (x->count > width / 2 - 1) * DOTS;
        return string_bytes(x->bytes,
                            MAX(0, MIN(x->count, (width - dots) / 2 - 1)),
                            dots);
    }
    case type_int:
        return string_ints(x->ints, x->count, width);
    case type_long:
        return string_longs(x->longs, x->count, width);
    case type_float:
        return string_floats(x->floats, x->count, width);
    case type_char:
        return string_chars(x->chars, x->count, width);
    case type_name:
        return string_names(x->names, x->count, width);
    default:
        assert_failed("string conversion for type not implemented");
    }
}


static void append_line(MValue* x, Value y, index at) {
    assert(!*x || (*x)->vector && (*x)->type == type_char && (*x)->count <= at);
    assert(!y || y->vector && y->type == type_char);
    index n = add_length(at, y ? y->count : DOTS);
    if (!*x) {
        *x = create_items(type_char, n);
        memset((*x)->chars, ' ', at);
    } else {
        index w = (*x)->count;
        resize(x, n);
        memset((*x)->chars + w, ' ', at - w);
    }
    if (y)
        memcpy((*x)->chars + at, y->chars, y->count);
    else
        memset((*x)->chars + at, '.', DOTS);
}


static MValue show_prepare(Value x, index width, index height) {
    // must return at least one line if height > 0

    if (!width || !height)
        return create_items(type_variant, 0);

    if (!x) // special for map separator
        return box(create_string(":", 1));

    if (!IS_MIXED(x) && x->type != type_map) {
        if (x->vector)
            return box(string_vector(x, width));
        else
            return box(repr(x));
    }

    bool map = x->type == type_map;
    index size = map ? x->map.key->count : x->count;

    bool all_bool = 1;
    if (!map)
        for (index i = 0; i < x->count; i++)
            if (x->mixed[i]->vector && x->mixed[i]->type != type_bool) {
                all_bool = 0;
                break;
            }

    bool reserved = 0;
    index rows = MIN(height, size), left = 0;
    MValue row[rows]; // each row is a list of lines
    index row_count[rows];

    index keep_j = 0;
    index keep_rows = rows, keep_left = 0;
    index keep_row_count[rows];

    for (index j = 0;;) {
        bool more = 0, flush_right = 1;
        index top = 0, extent = left;
        for (index i = 0; i < rows; i++) {
            row_count[i] = map ? 3 :
                           !all_bool && x->mixed[i]->vector ? x->mixed[i]->count
                                                            : -1;
            if (row_count[i] < 0) {
                if (j == 0) {
                    row[i] = show_prepare(x->mixed[i], width, height - top);
                    index w = MAX(width, DOTS);
                    for (index k = 0; k < row[i]->count; k++)
                        if (row[i]->mixed[k]->count > w) {
                            ((MValue)row[i]->mixed[k])->count = w;
                            memset(((MValue)row[i]->mixed[k])->chars + w - DOTS,
                                   '.', DOTS);
                        }
                }
            } else {
                if (j < row_count[i]) {
                    Value v = map ? j == 0 ? item(x->map.key,   i) :
                                    j == 2 ? item(x->map.value, i) : NULL
                                : item(x->mixed[i], j);
                    if (v && !IS_NUMERIC(v))
                        flush_right = 0;
                    MValue c = show_prepare(v, width - left, height - top);
                    if (j == 0)
                        row[i] = c;
                    else {
                        if (row[i]->count < c->count) {
                            index k = row[i]->count;
                            resize(&row[i], c->count);
                            for (; k < row[i]->count; k++)
                                row[i]->mixed[k] = NULL;
                        }
                        for (index k = 0; k < c->count; k++)
                            append_line((MValue*)&row[i]->mixed[k],
                                        c->mixed[k], left);
                    }
                    for (index k = 0; k < row[i]->count; k++)
                        if (extent < row[i]->mixed[k]->count)
                            extent = row[i]->mixed[k]->count;
                    if (j < row_count[i] - 1)
                        more = 1;
                } else
                    if (j == 0)
                        row[i] = box(create_string("()", 2));
            }
            top += row[i]->count;
            if (top > (i + 1 < size ? height - 1 : height)) {
                rows = i;
                break;
            }
        }

        if (flush_right)
            for (index i = 0; i < rows; i++)
                if (j < row_count[i])
                    for (index k = 0; k < row[i]->count; k++) {
                        MValue* s = (MValue*)&row[i]->mixed[k];
                        index w = (*s)->count;
                        if (w > left) {
                            index c = w - left;
                            resize(s, extent);
                            memmove((*s)->chars + (extent - c),
                                    (*s)->chars + left, c);
                            memset((*s)->chars + left, ' ',
                                   (extent - c) - left);
                        }
                    }

        left = extent + more;
        j++;

        if (left > width) {
            left = keep_left;
            j    = keep_j;
            rows = keep_rows;
            if (j)
                for (index i = 0; i < rows; i++) {
                    assert(row[i]->count >= keep_row_count[i]);
                    row[i]->count = keep_row_count[i];
                }
            for (index i = 0; i < rows; i++)
                for (index k = 0; k < row[i]->count; k++)
                    if (         row[i]->mixed[k] ->count > left)
                        ((MValue)row[i]->mixed[k])->count = left;

            if (!reserved) {
                width -= DOTS;
                reserved = 1;
            } else {
                for (index i = 0; i < rows; i++) {
                    if (j < row_count[i] && row[i]->count)
                        append_line((MValue*)&row[i]->mixed[0], NULL, left);
                }
                break;
            }
        }

        if (!more)
            break;

        if (reserved ? left <= width : width - left >= DOTS) {
            keep_left = left;
            keep_j    = j;
            keep_rows = rows;
            for (index i = 0; i < rows; i++)
                keep_row_count[i] = row[i]->count;
        }
    }

    bool incomplete = rows < (map ? x->map.value : x)->count;
    index k = 0;
    for (index i = 0; i < rows; i++)
        k += row[i]->count;
    assert(k <= (incomplete ? height - 1 : height));

    MValue r = create_items(type_variant, k + incomplete);
    k = 0;
    for (index i = 0; i < rows; i++)
        for (index j = 0; j < row[i]->count; j++)
            r->mixed[k++] = row[i]->mixed[j];
    if (incomplete)
        r->mixed[k] = create_string("...", 3); // different dots
    return r;
}


Value show(Value x) {
    index height, width = screen_size(&height);
    height = MAX(0, height - 2);

    x = show_prepare(x, width, height);
    bool incomplete = x->count > height;
    for (index i = 0; i < x->count && i < height - incomplete; i++) {
        index w = x->mixed[i]->count <= width ? x->mixed[i]->count
                                              : MAX(0, width - DOTS);
        printf("%.*s", (int)w, x->mixed[i]->chars);
        if (w < x->mixed[i]->count)
            for (index i = MIN(width, DOTS); i > 0; i--)
                putchar('.');
        putchar('\n');
    }
    if (incomplete && height)
        printf("...\n");

    return (Value)&untyped_null;
}


static Value repr_join(Value x, char left, char sep, char right) {
    assert(IS_MIXED(x));
    index chars = !!left + !!right;
    if (sep && x->count)
        chars = add_length(chars, x->count - 1);
    for (index i = 0; i < x->count; i++) {
        assert(x->mixed[i]->vector && x->mixed[i]->type == type_char);
        chars = add_length(chars, x->mixed[i]->count);
    }

    MValue r = create_items(type_char, chars);
    char* t = r->chars;
    if (left)
        *t++ = left;
    for (index i = 0; i < x->count; i++) {
        if (sep && i)
            *t++ = sep;
        assert(x->mixed[i]->vector && x->mixed[i]->type == type_char);
        memcpy(t, x->mixed[i]->chars, x->mixed[i]->count);
        t += x->mixed[i]->count;
    }
    if (right)
        *t++ = right;
    assert(t == r->chars + chars);
    return r;
}


Value repr(Value x) {
    if (x == NULL)
        return create_items(type_char, 0); // used for type_proj
    if (x->vector)
        switch (x->type) {
        case type_variant: {
            MValue r = create_items(type_variant, x->count);
            for (index i = 0; i < x->count; i++)
                r->mixed[i] = repr(x->mixed[i]);
            return repr_join(r, '(', ';', ')');
        }
        case type_bool:
            if (x->count)
                return string_bools(x->bools, x->count, 0);
            else
                return create_string("0#0b", 4);
        case type_byte:
            return string_bytes(x->bytes, x->count, 0);
        case type_int:
            if (x->count)
                return string_ints(x->ints, x->count, -1);
            else
                return create_string("0#0", 3);
        case type_long:
            if (x->count)
                return string_longs(x->longs, x->count, -1);
            else
                return create_string("0#0j", 4);
        case type_float:
            if (x->count)
                return string_floats(x->floats, x->count, -1);
            else
                return create_string("0#0.", 4);
        case type_char:
            return string_chars(x->chars, x->count, -1);
        case type_name:
            if (x->count)
                return string_names(x->names, x->count, -1);
            else
                return create_string("0#`", 3);
        }
    else
        switch (x->type) {
        case type_bool:
            return string_bools(&x->_bool, 1, 0);
        case type_byte:
            return string_bytes(&x->_byte, 1, 0);
        case type_int:
            return repr_int(x->_int);
        case type_long:
            return repr_long(x->_long);
        case type_float:
            return repr_float(x->_float);
        case type_char:
            return string_chars(&x->_char, 1, -1);
        case type_name:
            return string_names(&x->_name, 1, -1);
        case type_map:
            return repr_join(cons(repr(x->map.key), repr(x->map.value)),
                             0, '!', 0);
        case type_func:
            return create_string("{/}", 3);
        case type_proj: {
            MValue r = create_items(type_variant, x->proj.count);
            for (index i = 0; i < r->count; i++)
                r->mixed[i] = repr(x->proj.args[i]);
            return join(repr(x->proj.func), repr_join(r, '[', ';', ']'));
        }
        case type_comp:
            return join(create_char('\''),
                        repr_join(cons(repr(x->comp[0]), repr(x->comp[1])),
                                  '[', ';', ']'));
        case type_verb_prime:
        case type_verb: {
            Verb verb = x->verb;
            if (verb < sizeof verbs / sizeof *verbs && verbs[verb].name) {
                MValue r = create_items(type_char, 1 + (x->type != type_verb));
                r->chars[0] = verbs[verb].name;
                if (x->type != type_verb)
                    r->chars[1] = ':';
                return r;
            } else
                return join(create_string("`verb$", 6),
                            repr_int(x->type == type_verb ? verb : -verb));
        }
        case type_clause: {
            Adverb adverb = x->clause.adverb;
            if (adverb < sizeof adverbs / sizeof *adverbs &&
                    adverbs[adverb].name) {
                MValue r = create_items(type_char, 1 + adverbs[adverb].colon);
                r->chars[0] = adverbs[adverb].name;
                if (adverbs[adverb].colon)
                    r->chars[1] = ':';
                return join(x->clause.verb ? repr(x->clause.verb)
                                           : create_string("`adverb${}", 10),
                            r);
            } else
                if (x->clause.verb)
                    return join(join(join(create_string("(`adverb$", 9),
                                          repr_int(adverb)),
                                          create_char(')')),
                                          repr(x->clause.verb));
                else
                    return join(create_string("`adverb$", 8), repr_int(adverb));
        }
        }
    assert_failed("string conversion for type not implemented");
}


Value string(Value x) {
    if (x->vector) {
        MValue r = create_items(type_variant, x->count);
        for (index i = 0; i < x->count; i++)
            r->mixed[i] = string(item(x, i));
        return r;
    }
    switch (x->type) {
    case type_name:
        return create_stringz(x->_name);
    case type_map:
        return create_map(x->map.key, string(x->map.value));
    default:
        return repr(x);
    }
}
