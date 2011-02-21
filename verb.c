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

#include "verb.h"

#include "adverb.h"
#include "alloc.h"
#include "apply.h"
#include "arith.h"
#include "error.h"
#include "func.h"
#include "parse.h"
#include "string.h"
#include "sys.h"

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>

#define index index_hide /* index() should be in string.h anyway */
#include <string.h>
#undef index


static Value rank_error(Value x) {
    error(error_rank);
}


static Value binary_error(Value x, Value y) {
    error(error_rank);
}


static Value variadic_error(index n, const Value* p) {
    error(error_rank);
}


Value left(Value x) {
    return x;
}


Value right(Value x, Value y) {
    return y;
}


Value variadic_right(index n, const Value* p) {
    assert(n > 2);
    return p[n-1];
}


Value type(Value x) {
    return create_int(IS_MIXED(x) ? 0 :
                      x->vector || !types[x->type].vectorable ? x->type
                                                              : -x->type);
}


Value enlist(Value x) {
    MValue r;
    if (!x->vector && types[x->type].vectorable) {
        r = create_items(x->type, 1);
        COPY(r->items, ITEM(x), types[x->type].size);
    } else {
        r = create_items(type_variant, 1);
        r->mixed[0] = x;
    }
    return r;
}


Value join(Value x, Value y) {
    if (x->type == type_map && y->type == type_map)
        return create_map(join(x->map.key,   y->map.key),
                          join(x->map.value, y->map.value));

    index nx = x->vector ? x->count : 1,
          ny = y->vector ? y->count : 1,
          n = add_length(nx, ny);

    MValue r;
    if (x->type == y->type && types[x->type].vectorable) {
        size_t size = types[x->type].size;
        short offset = types[x->type].offset;
        r = create_items(x->type, n);
        COPIES(r->items,             x->vector ? x->items : x->item + offset,
               size, nx);
        COPIES(r->items + size * nx, y->vector ? y->items : y->item + offset,
               size, ny);
    } else {
        // automatically strengthen
        if (ny == 0)
            return x->vector ? x : enlist(x);
        if (nx == 0)
            return y->vector ? y : enlist(y);

        r = create_items(type_variant, n);
        if (x->vector)
            for (index i = 0; i < nx; i++)
                r->mixed[i] = item(x, i);
        else
            r->mixed[0] = x;
        if (y->vector)
            for (index i = 0; i < ny; i++)
                r->mixed[nx + i] = item(y, i);
        else
            r->mixed[nx] = y;
    }
    return r;
}


Value variadic_join(index n, const Value* p) {
    assert(n > 0); // technically n > 2 for a variadic verb, but we weaken the
                   // requirement so that raze() can call this easier

    int type = -1;
    index m = 0;
    for (index i = 0; i < n; i++) {
        Value v = p[i];
        if (type != v->type && !(v->vector && !v->count))
            if (type == -1)
                type = v->type;
            else
                type = -2;
        m = add_length(m, v->vector ? v->count : 1);
    }

    if (type == -1) {
        assert(m == 0);
        return (Value)&empty;
    }

    if (type == type_map) {
        Value q[n];
        for (index i = 0; i < n; i++)
            q[i] = p[i]->map.key;
        Value key = variadic_join(n, q);
        for (index i = 0; i < n; i++)
            q[i] = p[i]->map.value;
        return create_map(key, variadic_join(n, q));
    }

    MValue r;
    if (type >= 0 && types[type].vectorable) {
        size_t size =  types[type].size;
        short offset = types[type].offset;
        r = create_items(type, m);
        m = 0;
        for (index i = 0; i < n; i++) {
            Value v = p[i];
            index c = v->vector ? v->count : 1;
            COPIES(r->items + size * m, v->vector ? v->items : v->item + offset,
                   size, c);
            m += c;
        }
    } else {
        r = create_items(type_variant, m);
        m = 0;
        for (index i = 0; i < n; i++) {
            Value v = p[i];
            if (v->vector)
                for (index j = 0; j < v->count; j++)
                    r->mixed[m++] = item(v, j);
            else
                r->mixed[m++] = v;
        }
    }
    return r;
}


Value raze(Value p) {
    if (!IS_MIXED(p) || !p->count)
        return p;
    return variadic_join(p->count, p->mixed);
}


static Value primed_raze(Value x, Value y) {
    // fixme: possibly optimize
    return join(x, raze(y));
}


Value count(Value x) {
    return create_index(x->vector           ? x->count :
                        x->type == type_map ? x->map.value->count : 1);
}


#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define ABS(x) ((x) < 0 ? -(x) : (x))

Value take(Value x, Value y) {
    if (y->type == type_map)
        return create_map(take(x, y->map.key), take(x, y->map.value));

    index n = as_index(x);
    index count = ABS(n); // assume something about overflow
    check_length(count);

    size_t size = types[y->type].size;
    MValue r = create_items(y->type, count);
    if (y->vector) {
        if (n >= 0)
            for (index i = 0; i < count; i += y->count)
                COPIES(r->items + size * i, y->items,
                       size, MIN(y->count, count-i));
        else
            for (index i = count; i > 0; i -= y->count)
                COPIES(r->items + size * MAX(0, i - y->count),
                       y->items + size * MAX(0, y->count - i),
                       size, MIN(y->count, i));
    } else {
        short offset = types[y->type].offset;
        for (index i = 0; i < count; i++)
            COPY(r->items + size * i, y->item + offset, size);
    }
    return r;
}


Value drop(Value x, Value y) {
    if (!y->vector) {
        if (y->type == type_map)
            return create_map(drop(x, y->map.key), drop(x, y->map.value));

        if (!x->vector)
            if (x->type == type_map) {
                y = create_index(find_item(x->map.key, y));
                return create_map(drop(x->map.key, y), drop(x->map.value, y));
            } else
                error(error_type);

        index i = as_index(y);
        if (i < 0 || i >= x->count)
            error(error_index);

        size_t size = types[x->type].size;
        MValue r = create_items(x->type, x->count-1);
        COPIES(r->items,            x->items,                  size, i);
        COPIES(r->items + size * i, x->items + size * (i + 1), size,
               x->count - (i + 1));
        return r;
    }

    if (x->vector) {
        MValue r = create_items(type_variant, x->count);
        if (x->count) {
            index j = item_as_index(x, 0);
            if (j < 0)
                error(error_index);
            for (index i = 0; i < x->count-1; i++) {
                index k = item_as_index(x, i+1);
                if (k < j)
                    error(k < 0 ? error_index : error_length);
                r->mixed[i] = subvector(y, MIN(j, y->count),
                                           MIN(k, y->count) - MIN(j, y->count));
                j = k;
            }
            r->mixed[x->count-1] = subvector(y, MIN(j, y->count),
                                                y->count - MIN(j, y->count));
        }
        return r;
    } else {
        index n = as_index(x);
        if (n >= 0) {
            if (n < y->count)
                return subvector(y, n, y->count - n);
        } else
            if (-n < y->count)
                return subvector(y, 0, y->count - -n);
        return create_items(y->type, 0);
    }
}


static int flip_item_type(Value x, index j) {
    if (IS_MIXED(x))
        return x->mixed[j]->vector ? -1 : x->mixed[j]->type;
    else
        return x->type;
}


Value flip(Value x) {
    if (!IS_MIXED(x))
        error(error_type);
    index n = x->count;
    if (!n)
        return x;

#ifndef NSHORTCUT
    int matrix_type = x->mixed[0]->type;
#endif
    index m = -1;
    for (index i = 0; i < n; i++) {
#ifndef NSHORTCUT
        if (matrix_type != x->mixed[i]->type)
            matrix_type = -1;
#endif
        if (x->mixed[i]->vector)
            if (m < 0)
                m = x->mixed[i]->count;
            else if (m != x->mixed[i]->count)
                error(error_shape);
    }
    if (m < 0)
        error(error_type);

    MValue r = create_items(type_variant, m);
#ifndef NSHORTCUT
    if (matrix_type >= 0) { // matrix mode
        size_t size  = types[matrix_type].size;
        short offset = types[matrix_type].offset;
        for (index j = 0; j < m; j++)
            r->mixed[j] = create_items(matrix_type, n);
        for (index i = 0; i < n; i++) {
            Value v = x->mixed[i];
            for (index j = 0; j < m; j++)
                COPY(((MValue)r->mixed[j])->items + size * i,
                     v->vector ? v->items + size * j
                               : v->item  + offset, size);
        }
    } else
#endif
        for (index j = 0; j < m; j++) {
            int type = flip_item_type(x->mixed[0], j);
            if (type < 0 || !types[type].vectorable)
                goto mixed;
            for (index i = 1; i < n; i++)
                if (type != flip_item_type(x->mixed[i], j))
                    goto mixed;

            MValue s = create_items(type, n);
            size_t size  = types[type].size;
            short offset = types[type].offset;
            for (index i = 0; i < n; i++) {
                Value v = x->mixed[i];
                assert(!(IS_MIXED(v) && v->mixed[j]->vector));
                COPY(s->items + i * size,
                     IS_MIXED(v) ? v->mixed[j]->item + offset :
                     v->vector   ? v->items + size * j :
                                   v->item  + offset, size);
            }
            goto next;

        mixed:
            s = create_items(type_variant, n);
            for (index i = 0; i < n; i++)
                s->mixed[i] =
                    x->mixed[i]->vector ? item(x->mixed[i], j) : x->mixed[i];

        next:
            r->mixed[j] = s;
        }

    return r;
}


Value last(Value x) {
    if (x->vector)
        return item_null(x, x->count-1);
    else if (x->type == type_map)
        return last(x->map.value);
    else
        return x;
}


Value first(Value x) {
    if (x->vector)
        return item_null(x, 0);
    else if (x->type == type_map)
        return first(x->map.value);
    else
        return x;
}


Value reverse(Value x) {
    if (!x->vector)
        return x;
    index n = x->count;
    MValue r = create_items(x->type, n);
    size_t size = types[x->type].size;
    for (index i = 0; i < n; i++)
        COPY(r->items + i * size, x->items + (n-1 - i) * size, size);
    return r;
}


Value element(Value x, Value y) {
    if (!y->vector)
        error(error_type);
    switch (y->count) {
    case 0:
        return x;
    case 1:
        return apply(x, item(y, 0));
    case 2: {
        Value arg_x = item(y, 0), arg_y = item(y, 1);
        if (!IS_NULL(arg_x) && !IS_NULL(arg_y))
            return call_binary(x, arg_x, arg_y); // c. pass
        // falls through
    }
    default: {
        bool nulls = 0;
        Value args[y->count];
        for (index i = 0; i < y->count; i++) {
            args[i] = item(y, i);
            if (IS_NULL(args[i]))
                args[i] = NULL, nulls = 1;
        }
        return nulls ? project(x, y->count, args)
                     :    call(x, y->count, args); // c. pass
    }
    }
}


Value value(Value x) {
    if (x->type == type_map)
        return x->map.value;
    else if (IS_CALLABLE(x))
        return apply(x, (Value)&untyped_null); // c. pass
    else if (IS_MIXED(x) || x->vector && x->type == type_char)
        return eval(x); // c. pass
    else
        error(error_todo);
}


Value bang(Value x, Value y) {
    if (x->vector) {
        if (!y->vector)
            error(error_type);
        if (x->count != y->count)
            error(error_length);
        return create_map(x, y);
    } else
        return modulo(y, x);
}


Value range(Value x) {
    if (x->type == type_map)
        return x->map.key;

    if (x->vector && x->count == 2) {
        index m = item_as_index(x, 0),
              k = item_as_index(x, 1);
        if (m < 0 || k < 0)
            error(error_index);
        index n = k - m;
        check_length(n);
        MValue r = create_items(type_index, n);
        for (index i = 0; i < n; i++)
            r->indexes[i] = i + m;
        return r;
    }

    index n = as_index(x);
    if (n >= 0) {
        check_length(n);
        MValue r = create_items(type_index, n);
        for (index i = 0; i < n; i++)
            r->indexes[i] = i;
        return r;
    } else {
        index m = 1;
        for (index i = 0; i > n; i--) {
            if (m >= index_max / (1 - i))
                error(error_length);
            m *= 1 - i;
        }

        index p[n = -n];
        for (index i = 0; i < n; i++)
            p[i] = i;

        MValue r = create_items(type_variant, m);
        for (index i = 0, j, k;;) {
            MValue s = create_items(type_index, n);
            COPIES(s->items, p, sizeof *p, n);
            r->mixed[i] = s;
            if (++i == m)
                break;
            for (j = n-2; p[j] > p[j+1]; j--);
            for (k = n-1; p[j] > p[k];   k--);
            index t = p[j]; p[j] = p[k]; p[k] = t;
            for (k = n; --k > ++j;)
                  t = p[j], p[j] = p[k], p[k] = t;
        }
        return r;
    }
}


Value where(Value x) {
    if (x->type == type_map)
        return apply(x->map.key, where(x->map.value));
    if (!x->vector)
        error(error_type);

#ifndef NSHORTCUT
    if (x->type == type_bool) {
        index n = 0;
        for (index i = 0; i < x->count; i++)
            if (x->bools[i])
                n++;
        MValue r = create_items(type_index, n);
        n = 0;
        for (index i = 0; i < x->count; i++)
            if (x->bools[i])
                r->indexes[n++] = i;
        assert(n == r->count);
        return r;
    }
    if (x->type == type_index) {
        index n = 0;
        for (index i = 0; i < x->count; i++)
            n = add_length(n, x->indexes[i]);
        MValue r = create_items(type_index, n);
        n = 0;
        for (index i = 0; i < x->count; i++)
            for (index j = 0; j < x->indexes[i]; j++)
                r->indexes[n++] = i;
        assert(n == r->count);
        return r;
    }
#endif

    index n = 0;
    for (index i = 0; i < x->count; i++)
        n = add_length(n, item_as_index(x, i));
    MValue r = create_items(type_index, n);
    n = 0;
    for (index i = 0; i < x->count; i++) {
        index m = item_as_index(x, i);
        for (index j = 0; j < m; j++)
            r->indexes[n++] = i;
    }
    assert(n == r->count);
    return r;
}


Value group(Value x) {
    if (!x->vector)
        if (x->type == type_map) {
            Value grouped = group(x->map.value);
            return create_map(grouped->map.key,
                              items(x->map.key, grouped->map.value));
        } else
            error(error_type);

    MValue key   = create_items(x->type, 0),
           value = create_items(type_variant, 0);

    // fixme: shortcuts
    for (index i = 0; i < x->count; i++) {
        Value v = item(x, i);
        index j = find_item(key, v);
        if (j == key->count) {
            push(&key, v);
            push(&value, create_items(type_index, 0));
        }
        push_index((MValue*)&value->mixed[j], i);
    }

    return create_map(key, value);
}


struct sort_info {
    const char* items;
    size_t size;
    int (*compare)(const char*, const char*);
    int sign;
};

static bool sort_less(const struct sort_info* info, index i, index j) {
    int c = info->compare(info->items + info->size * i,
                          info->items + info->size * j);
    return c ? info->sign * c < 0 : i < j;
}

// float an element v from position i up to its correct position
static void heap_float(const struct sort_info* info,
                      index* a, index i, index v) {
    index j;
    for (; i; i = j) {
        j = (i-1)/2;
        if (!sort_less(info, a[j], v)) // a[j] > v
            break;
        a[i] = a[j];
    }
    a[i] = v;
}

// sink a hole from position 0 down to its correct position,
// returning the position
static index heap_sink_hole(const struct sort_info* info, index* a, index n) {
    index i, j;
    for (i = 0; i < n/2; i = j) {
        j = i*2+1;
        if (j+1 < n && sort_less(info, a[j], a[j+1])) // a[j] < a[j+1]
            ++j;
        a[i] = a[j];
    }
    return i;
}

static void heap_sort(struct sort_info* info, index* a, index n) {
    for (index i = 0; i < n; i++)
        heap_float(info, a, i, i);
    while (--n > 0) {
        index v = a[n]; a[n] = a[0];
        heap_float(info, a, heap_sink_hole(info, a, n), v);
    }
}

static Value order(Value x, int sign) {
    if (!x->vector)
        if (x->type == type_map)
            return items(x->map.key, order(x->map.value, sign));
        else
            error(error_type);
    struct sort_info info =
        { x->items, types[x->type].size, types_conv[x->type].compare, sign };

    MValue r = create_items(type_index, x->count);
    heap_sort(&info, r->indexes, x->count);
    return r;
}

Value order_asc( Value x) { return order(x,  1); }
Value order_desc(Value x) { return order(x, -1); }


Value unique(Value x) {
    if (!x->vector)
        return draw(x);

    int (*compare)(const char*, const char*) = types_conv[x->type].compare;
    size_t size = types[x->type].size;

    MValue r = create_items(type_index, 0);
    for (index i = 0; i < x->count; i++) {
        index n = r->count;
        for (index j = 0; j < n; j++)
            if (!compare(x->items + size * r->indexes[j], x->items + size * i))
                goto next;
        push_index(&r, i);
        // length checking is actually unnecessary since r is not longer than x
    next:;
    }
    return r; // mixed cannot be strengthened
}


#define BM_COUNT(as_n) as_n = n;
#define BM_CALL(v, i)  v = f(x->vector ? item(x, i) : x,  \
                             y->vector ? item(y, i) : y);

static Value binary_mixed(Value (*f)(Value, Value), Value x, Value y, index n) {
    MValue r;
    AUTO_STRENGTHEN(r, BM_COUNT, BM_CALL, BM_CALL,);
    return r;
}


#define PICK(name, comp)                                                       \
Value name(Value x, Value y) {                                                 \
    if (!x->vector && !y->vector)                                              \
        return compare(x, y) comp 0 ? x : y;                                   \
                                                                               \
    index n = x->vector ? x->count : y->count;                                 \
    if (y->vector && n != y->count)                                            \
        error(error_length);                                                   \
                                                                               \
    Type type = y->type;                                                       \
    if (type != x->type || IS_MIXED(y))                                        \
        return binary_mixed(name, x, y, n);                                    \
                                                                               \
    const char* x_items = x->vector ? x->items : x->item + types[type].offset; \
    const char* y_items = y->vector ? y->items : y->item + types[type].offset; \
    int (*compare)(const char*, const char*) = types_conv[type].compare;       \
    size_t size = types[type].size;                                            \
                                                                               \
    MValue r = create_items(type, n);                                          \
    for (index i = 0; i < n; i++) {                                            \
        const char* x_item = x_items + x->vector * size * i;                   \
        const char* y_item = y_items + y->vector * size * i;                   \
        COPY(r->items + size * i,                                              \
             compare(x_item, y_item) comp 0 ? x_item : y_item, size);          \
    }                                                                          \
    return r;                                                                  \
}

PICK(binary_min, <)
PICK(binary_max, >)


Value fill(Value x, Value y) {
    if (!y->vector) {
        if (!x->vector)
            return is_null(y) ? x : y;
        else
            error(error_type);
    }

    index n = y->count;
    if (x->vector && x->count != n)
        error(error_length);

    Type type = y->type;
    if (x->type != type || IS_MIXED(y))
        return binary_mixed(fill, x, y, n);

    const char* x_items = x->vector ? x->items : x->item + types[type].offset;
    bool (*null_test)(const char*) = types_conv[type].is_null;
    size_t size = types[type].size;

    MValue r = NULL;
    for (index i = 0; i < y->count; i++)
        if (null_test(y->items + size * i)) {
            if (!r)
                r = copy(y);
            COPY(r->items + size * i, x_items + x->vector * size * i, size);
        }
    return r ? r : y;
}


#define UM_COUNT(n) n = x->count;
#define UM_CALL(v, i)  v = f(x->mixed[i]);

static Value unary_mixed(Value (*f)(Value), Value x) {
    MValue r;
    AUTO_STRENGTHEN(r, UM_COUNT, UM_CALL, UM_CALL,);
    return r;
}


Value null(Value x) {
    if (!x->vector)
        if (x->type == type_map)
            return create_map(x->map.key, null(x->map.value));
        else
            return create_bool(is_null(x));

    if (IS_MIXED(x))
        return unary_mixed(null, x);

    bool (*null_test)(const char*) = types_conv[x->type].is_null;
    size_t size = types[x->type].size;

    MValue r = create_items(type_bool, x->count);
    for (index i = 0; i < x->count; i++)
        r->bools[i] = null_test(x->items + size * i);
    return r;
}


Value find(Value x, Value y) {
    if (IS_MIXED(x) || !y->vector)
        return create_index(find_item(x, y));

    Type type = x->type;
    if (y->type != type)
        error(error_type);
    int (*compare)(const char*, const char*) = types_conv[type].compare;
    size_t size = types[type].size;

    MValue r = create_items(type_index, y->count);
    for (index i = 0; i < y->count; i++) {
        index j;
        for (j = 0; j < x->count; j++)
            if (!compare(x->items + size * j, y->items + size * i))
                break;
        r->indexes[i] = j;
    }
    return r;
}


Value identical(Value x, Value y) {
    return create_bool(!compare(x, y));
}


static Value binary_list(Value x, Value y) {
    // automatically strengthen
    if (x->vector || y->vector || x->type != y->type ||
            !types[x->type].vectorable)
        return cons(x, y);

    size_t size = types[x->type].size;
    short offset = types[x->type].offset;
    MValue r = create_items(x->type, 2);
    COPY(r->items,        x->item + offset, size);
    COPY(r->items + size, y->item + offset, size);
    return r;
}


static Value variadic_list(index n, const Value* p) {
    assert(n > 2);

    // automatically strengthen
    Type type = p[0]->type;
    if (p[0]->vector || !types[type].vectorable)
        goto mixed;
    for (index i = 1; i < n; i++)
        if (p[i]->vector || p[i]->type != type)
            goto mixed;

    size_t size = types[type].size;
    short offset = types[type].offset;
    MValue r = create_items(type, n);
    for (index i = 0; i < n; i++)
        COPY(r->items + size * i, p[i]->item + offset, size);
    return r;

mixed:
    r = create_items(type_variant, n);
    COPIES(r->items, p, sizeof *p, n);
    return r;
}


static Value compose_replace(Value x, bool prime, Verb what, Verb with) {
    if (x->type == (prime ? type_verb_prime : type_verb) && x->verb == what)
        return prime ? (Value)&verbs[with].literal_prime
                     : (Value)&verbs[with].literal;
    else
        switch (x->type) {
        case type_proj: {
            Value func = compose_replace(x->proj.func, prime, what, with);
            if (func) {
                MValue r = copy(x);
                r->proj.func  = func;
                return r;
            }
            break;
        }
        case type_comp: {
            Value head = compose_replace(x->comp[0], prime, what, with);
            if (head) {
                MValue r = copy(x);
                r->comp[0] = head;
                return r;
            }
            break;
        }
        }
    return NULL;
}


static Value compose_replace_adverb(Value x, Adverb what, Adverb with) {
    if (x->type == type_clause && x->clause.adverb == what) {
        MValue r = copy(x);
        r->clause.adverb = with;
        return r;
    } else
        switch (x->type) {
        case type_proj: {
            Value func = compose_replace_adverb(x->proj.func, what, with);
            if (func) {
                MValue r = copy(x);
                r->proj.func  = func;
                return r;
            }
            break;
        }
        case type_comp: {
            Value head = compose_replace_adverb(x->comp[0], what, with);
            if (head) {
                MValue r = copy(x);
                r->comp[0] = head;
                return r;
            }
            break;
        }
        }
    return NULL;
}


Value compose(Value x, Value y) {
    if (!IS_CALLABLE(y))
        error(error_type);

    if (x->type == type_verb_prime) {
        Value r;
        switch (x->verb) {
        case verb_line:
            if (r = compose_replace(y, 0, verb_divide, verb_divide_int))
                return r;
            break;
        case verb_times:
            if (r = compose_replace(y, 1, verb_or, verb_first))
                return r;
            break;
        case verb_tilde:
            if (r = compose_replace(y, 0, verb_equal, verb_not_equal))
                return r;
            if (r = compose_replace(y, 0, verb_less, verb_not_less))
                return r;
            if (r = compose_replace(y, 0, verb_greater, verb_not_greater))
                return r;
            break;
        case verb_hash:
            if (r = compose_replace_adverb(y, adverb_trace, adverb_trace_count))
                return r;
            if (r = compose_replace_adverb(y, adverb_binary_scan,
                                              adverb_binary_scan_count))
                return r;
            if (r = compose_replace_adverb(y, adverb_variadic_scan,
                                              adverb_variadic_scan_count))
                return r;
            break;
        }
    }

    MValue r = create_item(type_comp);
    r->comp[0] = x;
    r->comp[1] = y;
    return r;
}


Value cast(Value x, Value y) {
    if (x->vector || x->type != type_name)
        return error_type;

    if (IS_MIXED(y)) {
        // fixme: optimize since strengthening is guaranteed possible
        MValue r = create_items(type_variant, y->count);
        for (index i = 0; i < y->count; i++)
            r->mixed[i] = cast(x, y->mixed[i]);
        return strengthen(r);
    } else {
#ifndef NFUNNY
        if (x->_name == name_bool && !y->vector && y->type == type_name &&
                                     !strcmp(y->_name, "filenotfound")) {
            MValue r = create_item(type_bool);
            r->_bool = 2;
            return r;
        }
#endif
        #define CAST_TYPE(vtype)                                              \
        if (x->_name == name_##vtype) {                                       \
            vtype##_type (*convert)(const char*) =                            \
                types_conv[y->type]._##vtype;                                 \
            if (y->vector) {                                                  \
                size_t size = types[y->type].size;                            \
                MValue r = create_items(type_##vtype, y->count);              \
                for (index i = 0; i < y->count; i++)                          \
                    r->vtype##s[i] = convert(y->items + size * i);            \
                return r;                                                     \
            } else                                                            \
                return                                                        \
                    create_##vtype(convert(y->item + types[y->type].offset)); \
        }
        CAST_TYPE(bool)
        CAST_TYPE(byte)
        CAST_TYPE(int)
        CAST_TYPE(long)
        CAST_TYPE(float)
        if (x->_name == name_char)
            error(error_todo);
        if (x->_name == name_name || is_null_name(x->_name)) {
            if (!y->vector || y->type != type_char)
                error(error_type);
            // fun fact: Darwin doesn't have strnlen()
            if (memchr(y->chars, 0, y->count))
                error(error_type);
            return create_name(y->chars, y->count);
        }
        if (x->_name == name_verb && !y->vector && y->type == type_int) {
            int verb = ABS(y->_int);
            if (verb < 0 || verb >= sizeof verbs / sizeof *verbs
                         || verbs[verb].name)
                error(error_range);
            return y->_int >= 0 ? (Value)&verbs[verb].literal
                                : (Value)&verbs[verb].literal_prime;
        }
        if (x->_name == name_adverb)
            error(error_todo);
        error(error_type);
    }
}


Value throw(Value x) {
    error(x);
}


static Value catch_call(Value f) {
    return apply(f->mixed[0], f->mixed[1]);
}


static Value catch_error(Value f, Value error) {
    return apply(f->mixed[2], error);
}


static Value catch(index n, const Value* p) {
    assert(n > 2);
    if (n != 3)
        error(error_rank);

    MValue f = create_items(type_variant, n);
    COPIES(f->items, p, sizeof *p, n);
    hold(f); // c.: only need to hold f->mixed[2]

    Value x = protected(catch_call, f, catch_error, -1);
    release(1);
    return x;
}


static Value unary_collect(Value x) {
    collect();
    return (Value)&untyped_null;
}


MValue globals_key;   // names
MValue globals_value; // mixed

static Value global_read(Value x) {
    index i = find_item(globals_key, x);
    if (i < globals_value->count)
        return globals_value->mixed[i];
    else
        error(x);
}


static Value global_write(Value x, Value y) {
    index i = find_item(globals_key, x);
    if (i < globals_value->count)
        globals_value->mixed[i] = y;
    else {
        // find_item checks that x is suitable
        push(&globals_key,   x);
        push(&globals_value, y);
    }
    return y;
}


void globals_init() {
    globals_key   = create_items(type_name,    0);
    globals_value = create_items(type_variant, 0);

    hold_mvalue(&globals_key);
    hold_mvalue(&globals_value);

    global_write(create_namez("repr"),
            (Value)&verbs[verb_repr].literal_prime);
    global_write(create_namez("show"),
            (Value)&verbs[verb_show].literal_prime);
    global_write(create_namez("lex"),
            (Value)&verbs[verb_lex]. literal_prime);
    global_write(create_namez("parse"),
            (Value)&verbs[verb_parse].literal_prime);
    global_write(create_namez("disasm"),
            (Value)&verbs[verb_disasm].literal_prime);
    global_write(create_namez("collect"),
            (Value)&verbs[verb_collect].literal_prime);
    global_write(create_namez("read"),
            (Value)&verbs[verb_read].literal_prime);
    global_write(create_namez("write"),
            (Value)&verbs[verb_write].literal);
    global_write(create_namez("mmap"),
            (Value)&verbs[verb_mmap].literal_prime);
    global_write(create_namez("time"),
            (Value)&verbs[verb_time].literal_prime);
}


static Value init_counter(Value x) {
     // this will be modified in place so make sure it's distinct
     // (specifically not a reference to one of the small int constants)
    MValue r = create_item(type_index);
    r->index = as_index(x);
    return r;
}


static Value init_closure(Value x, Value y) {
    assert(x->type == type_func && y->type == type_func);
    MValue r = create_item(type_func);
    r->func.code     = x->func.code;
    r->func.upvalues = y->func.upvalues;
    return r;
}


#define LITERAL(name) { type_verb_prime, 0, verb_##name }, \
                      { type_verb,       0, verb_##name }

const struct verb verbs[] = {
    // normal verbs
    { ':',  LITERAL(null)    },
    { '@',  LITERAL(at)      },
    { '.',  LITERAL(dot)     },
    { ',',  LITERAL(comma)   },
    { '#',  LITERAL(hash)    },
    { '_',  LITERAL(line)    },
    { '+',  LITERAL(plus)    },
    { '-',  LITERAL(minus)   },
    { '*',  LITERAL(times)   },
    { '%',  LITERAL(divide)  },
    { '!',  LITERAL(bang)    },
    { '&',  LITERAL(and)     },
    { '|',  LITERAL(or)      },
    { '~',  LITERAL(tilde)   },
    { '=',  LITERAL(equal)   },
    { '<',  LITERAL(less)    },
    { '>',  LITERAL(greater) },
    { '^',  LITERAL(hat)     },
    { '?',  LITERAL(query)   },
    { '\'', LITERAL(accent)  },
    { '$',  LITERAL(cast)    },

    // unnamed verbs
    { 0, LITERAL(list)           },
    { 0, LITERAL(divide_int)     },
    { 0, LITERAL(first)          },
    { 0, LITERAL(not_equal)      },
    { 0, LITERAL(not_less)       },
    { 0, LITERAL(not_greater)    },
    { 0, LITERAL(sum)            },
    { 0, LITERAL(raze)           },
    { 0, LITERAL(max)            },
    { 0, LITERAL(min)            },
    { 0, LITERAL(repr)           },
    { 0, LITERAL(show)           },
    { 0, LITERAL(lex)            },
    { 0, LITERAL(parse)          },
    { 0, LITERAL(disasm)         },
    { 0, LITERAL(collect)        },
    { 0, LITERAL(read)           },
    { 0, LITERAL(write)          },
    { 0, LITERAL(mmap)           },
    { 0, LITERAL(time)           },
    { 0, LITERAL(assign_item)    },
    { 0, LITERAL(assign_element) }
};


const struct verb_run verbs_run[] = {
    // normal verbs
    { left,          right,            variadic_right,   0, 0 },
    { type,          apply,            modify_item,      0, 1 },
    { value,         element,          modify_element,   1, 1 },
    { enlist,        join,             variadic_join,    0, 0 },
    { count,         take,             variadic_error,   0, 0 },
    { entier,        drop,             variadic_error,   0, 0 },
    { flip,          plus,             variadic_plus,    0, 0 },
    { neg,           minus,            variadic_error,   0, 0 },
    { last,          times,            variadic_error,   0, 0 },
    { invert,        divide,           variadic_error,   0, 0 },
    { range,         bang,             variadic_error,   0, 0 },
    { where,         binary_min,       variadic_error,   0, 0 },
    { reverse,       binary_max,       variadic_error,   0, 0 },
    { not,           identical,        variadic_error,   0, 0 },
    { group,         equal,            variadic_error,   0, 0 },
    { order_asc,     less,             variadic_error,   0, 0 },
    { order_desc,    greater,          variadic_error,   0, 0 },
    { null,          fill,             variadic_error,   0, 0 },
    { unique,        find,             variadic_error,   0, 0 },
    { throw,         compose,          catch,            0, 0 },
    { string,        cast,             variadic_error,   0, 0 },

    // unnamed verbs
    { rank_error,    binary_list,      variadic_list,    0, 0 },
    { rank_error,    divide_int,       variadic_error,   0, 0 },
    { first,         binary_error,     variadic_error,   0, 0 },
    { rank_error,    not_equal,        variadic_error,   0, 0 },
    { rank_error,    not_less,         variadic_error,   0, 0 },
    { rank_error,    not_greater,      variadic_error,   0, 0 },
    { sum,           primed_sum,       variadic_error,   0, 0 },
    { raze,          primed_raze,      variadic_error,   0, 0 },
    { max,           primed_max,       variadic_error,   0, 0 },
    { min,           primed_min,       variadic_error,   0, 0 },
    { repr,          binary_error,     variadic_error,   0, 0 },
    { show,          binary_error,     variadic_error,   0, 0 },
    { lex,           binary_error,     variadic_error,   0, 0 },
    { parse,         binary_error,     variadic_error,   0, 0 },
    { disasm,        binary_error,     variadic_error,   0, 0 },
    { unary_collect, binary_error,     variadic_error,   1, 0 },
    { read_file,     binary_error,     variadic_error,   0, 0 },
    { rank_error,    write_file,       variadic_error,   0, 0 },
    { mmap_file,     binary_error,     variadic_error,   0, 0 },
    { time_value,    binary_error,     variadic_error,   0, 0 },
    { NULL,          NULL,             assign_item,      0, 0 },
    { NULL,          NULL,             assign_element,   0, 0 },

    // opcode-only verbs
    { global_read,   NULL,             NULL,             0, 0 },
    { NULL,          global_write,     NULL,             0, 0 },
    { init_counter,  NULL,             NULL,             0, 0 },
    { NULL,          init_closure,     NULL,             0, 0 },
    { NULL,          scalar_plus,      NULL,             0, 0 },
    { NULL,          scalar_minus,     NULL,             0, 0 }
};
