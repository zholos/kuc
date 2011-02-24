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

#include "apply.h"

#include "adverb.h"
#include "alloc.h"
#include "code.h"
#include "error.h"
#include "func.h"
#include "verb.h"

#include <assert.h>
#include <stdio.h>

#define index index_hide /* index() should be in string.h anyway */
#include <string.h>
#undef index


Value items(Value x, Value y) {
    if (!x->vector)
        if (x->type == type_map)
            if (y->vector || y->type == type_map)
                return items(x->map.value, find(x->map.key, y));
            else
                return item_null(x->map.value, find_item(x->map.key, y));
        else
            error(error_type);

    if (!y->vector)
        if (y->type == type_map)
            return create_map(y->map.key, items(x, y->map.value));
        else
            return item_null(x, as_index(y));

    if (y->type == type_variant) { // i.e., probably includes vectors
        MValue r = create_items(type_variant, y->count);
        for (index i = 0; i < y->count; i++)
            r->mixed[i] = items(x, y->mixed[i]);
        return strengthen(r);
    }

    Type type = x->type;
    MValue r = create_items(type, y->count);
    if (type == type_variant) {
        for (index i = 0; i < y->count; i++)
            r->mixed[i] = item_null(x, item_as_index(y, i));
        return strengthen(r);
    } else {
        size_t size = types[type].size;
        for (index i = 0; i < y->count; i++) {
            index j = item_as_index(y, i);
            COPY(r->items + size * i,
                 j >= 0 && j < x->count ? x->items + size * j
                                        : (const char*)&types_conv[type].null,
                 size);
        }
        return r;
    }
}


Value apply(Value f, Value x) { // reaches c.
    if (f->vector || f->type == type_map)
        return items(f, x);

    switch (f->type) {
    case type_func:
        if (f->func.code->args == 1) {
            Value frame[f->func.code->frame];
            frame[0] = f;
            frame[1] = x;
            return run(frame); // c. p.
        } else
            return project_unary(f, x);
    case type_proj: {
        const Proj* proj = &f->proj;
#ifndef NSHORTCUT
        if (proj->func->type == type_verb ||
            proj->func->type == type_func && proj->func->func.code->args == 2) {
            // a useful projection for a binary function is either [x] or [;y]
            switch (proj->count) {
            case 1:
                return call_binary(proj->func, proj->args[0], x);
            case 2:
                if (!proj->args[0])
                    return call_binary(proj->func, x, proj->args[1]);
            }
        }
#endif
        Value args[add_length(proj->count, 1)];
        for (index i = 0; i < proj->count; i++)
            if (proj->args[i])
                args[i] = proj->args[i];
            else {
                args[i] = x;
                for (i++; i < proj->count; i++)
                    if (!(args[i] = proj->args[i])) {
                        // empty was filled but there are more empty args
                        for (i++; i < proj->count; i++)
                            args[i] = proj->args[i];
                        return project(proj->func, proj->count, args);
                    }
                // empty was filled and there are no more empty args
                return call(proj->func, proj->count, args); // c. p.
            }
        // there were no empty args in the projection, so push onto end
        args[proj->count] = x;
        return call(proj->func, proj->count + 1, args); // c. p.
    }
    case type_comp: {
        index v = min_valence(f->comp[1]);
        if (1 >= v) {
            Value h = f->comp[0];
            hold(h);
            x = apply(f->comp[1], x); // c. p. f part, x
            release(1);
            return apply(h, x); // c. p.
        } else
            return project_unary(f, x);
    }
    case type_verb_prime:
        return verbs_run[f->verb].unary(x); // c. p.
    case type_verb:
        return project_unary(f, x);
    case type_clause:
        return adverbs_run[f->clause.adverb].unary(f->clause.verb, x); // c. p.
    default:
        error(error_type);
    }
}


Value modify_item(index n, const Value* p) { // reaches c.
    assert(n > 2);
    if (n > 4)
        error(error_rank);
    hold_array(n, p);

    Value r;
    if (n == 3)
        r = apply(p[2], apply(p[0], p[1])); // c.
#ifndef NSHORTCUT
    else if (p[2]->type == type_verb && p[2]->verb == verb_null)
        r = p[3];
#endif
    else
        r = call_binary(p[2], apply(p[0], p[1]), p[3]); // c.

    MValue x = copy(p[0]);
    amend(&x, p[1], r);
    release_array(1);
    return x;
}


Value modify_element(index n, const Value* p) {
    error(error_todo);
}


Value assign_item(index n, const Value* p) {
    assert(n == 3);
    MValue x = copy(p[0]);
    amend(&x, p[2], p[1]);
    return x;
}


static Value assign_element_recurse(Value x, Value y, index n, const Value* i) {
    if (n == 1) {
        if (*i) {
            MValue r = copy(x);
            amend(&r, *i, y);
            return r;
        } else
            return y;
    }

    if (*i) {
        MValue r = copy(x);
        if ((*i)->vector) {
            if (y->vector && y->count != (*i)->count)
                error(error_length);
            for (index j = 0; j < (*i)->count; j++) {
                Value k = item(*i, j);
                amend(&r, k, assign_element_recurse(items(r, k),
                    y->vector ? item(y, j) : y, n-1, i+1));
            }
        } else
            amend(&r, *i, assign_element_recurse(items(r, *i), y, n-1, i+1));
        return r;
    } else {
        if (!x->vector)
            if (x->type == type_map)
                return create_map(x->map.key,
                    assign_element_recurse(x->map.value, y, n, i));
            else
                return assign_element_recurse(x, y, n-1, i+1);

        MValue r = copy(x);
        if (y->vector && y->count != x->count)
            error(error_length);
        for (index j = 0; j < x->count; j++)
            amend_vector(&r, j, assign_element_recurse(item(r, j),
                y->vector ? item(y, j) : y, n-1, i+1));
        return r;
    }
}


Value assign_element(index n, const Value* p) {
    // NULL elements of p denote projection
    assert(n > 2); // object, value, indexes
    return assign_element_recurse(p[0], p[1], n-2, p+2);
}


#define MAX(x, y) ((x) > (y) ? (x) : (y))

index valence(Value f) {
    if (f->vector)
        return 1;

    switch (f->type) {
    case type_func:
        return f->func.code->args;
    case type_proj: {
        index u = valence(f->proj.func), n = f->proj.count, v = MAX(u, n);
        for (index i = 0; i < n; i++)
            if (f->proj.args[i])
                v--;
        return v;
    }
    case type_comp:
        return valence(f->comp[1]);
    case type_verb_prime:
        return 1;
    case type_verb:
        return 2;
    case type_clause:
        return adverbs[f->clause.adverb].valence(f->clause.verb);
    default:
        return 1; // nothing has zero valence
    }
}


index min_valence(Value f) {
    switch (f->type) {
    case type_proj: {
        index u = min_valence(f->proj.func), n = f->proj.count, v = MAX(u, n);
        for (index i = 0; i < n; i++)
            if (f->proj.args[i])
                v--;
        return v;
    }
    case type_comp:
        return min_valence(f->comp[1]);
    case type_clause:
        return adverbs[f->clause.adverb].min_valence(f->clause.verb);
    default:
        return valence(f);
    }
}


static Value create_proj(Value f, index n, const Value* p) {
    MValue proj = create_item(type_proj);
    proj->proj.func = f;
    proj->proj.count = n;
    proj->proj.args = alloc(sizeof *p * n, alloc_normal);
    memcpy(proj->proj.args, p, sizeof *p * n);
    return proj;
}


#define PR_COUNT(n)      n = x->count;
#define PR_CALL(v, as_i) v = project_recurse(item(x, as_i), n-1, i+1);

static Value project_recurse(Value x, index n, const Value* i) { // reaches c.
    if (n == 1)
        return *i ? apply(x, *i) : x;

    if (*i) {
        if (IS_CALLABLE(x)) {
            index v = min_valence(x);
            if (n >= v) {
                for (index j = 1; j < n; j++)
                    if (!i[j])
                        return create_proj(x, n, i);
                v = valence(x);
                assert(v > 0);
                if (n > v) {
                    x = v == 1 ? apply(x, i[0]) : call(x, v, i); // c. p. x
                    return project_recurse(x, n-v, i+v);
                } else
                    return call(x, n, i); // c. p. x
            } else
                return create_proj(x, n, i);
        }

        x = items(x, *i);
        if ((*i)->vector) {
        all:
            assert(x->vector);
            hold(x);
            MValue r; hold_mvalue(&r);
            AUTO_STRENGTHEN(r, PR_COUNT, PR_CALL, PR_CALL, COLLECT())
            release_mvalue(1); release(1);
            return r;
        } else
            return project_recurse(x, n-1, i+1); // c. p. x
    } else {
        if (x->type == type_map)
            return create_map(x->map.key, project_recurse(x->map.value, n, i));
        if (IS_CALLABLE(x))
            return create_proj(x, n, i);
        if (!x->vector)
            error(error_type);
        goto all;
    }
}


Value project(Value f, index n, const Value* p) { // reaches c.
#ifndef NSHORTCUT
    if (IS_CALLABLE(f)) 
        return create_proj(f, n, p);
#endif

    hold_array(n, p); // c. tracks all args here so recurse doesn't have to
    Value r = project_recurse(f, n, p);
    release_array(1);
    return r;
}


Value project_unary(Value f, Value x) {
    MValue proj = create_item(type_proj);
    proj->proj.func = f;
    proj->proj.count = 1;
    proj->proj.args = alloc(sizeof *proj->proj.args, alloc_normal);
    proj->proj.args[0] = x;
    return proj;
}


#define CR_COUNT(n)      n = x->count;
#define CR_CALL(v, as_i) v = call_recurse(item(x, as_i), n-1, i+1);

static Value call_recurse(Value x, index n, const Value* i) { // reaches c.
    if (n == 1)
        return apply(x, *i);

    if (IS_CALLABLE(x)) {
        index v = min_valence(x);
        if (n >= v) {
            v = valence(x);
            assert(v > 0);
            if (n > v)
                return call_recurse(call(x, v, i), n-v, i+v); // c. p.
            else
                return call(x, n, i); // c. p. x
        } else
            return create_proj(x, n, i);
    }

    x = items(x, *i);
    if ((*i)->vector) {
        assert(x->vector);
        hold(x);
        MValue r; hold_mvalue(&r);
        AUTO_STRENGTHEN(r, CR_COUNT, CR_CALL, CR_CALL, COLLECT())
        release_mvalue(1); release(1);
        return r;
    } else
        return project_recurse(x, n-1, i+1); // c. p. x
}


Value call(Value f, index n, const Value* p) { // reaches c.
    // p must be complete (no nulls)
    switch (n) {
    case 0:
        assert_failed("too few arguments for call");
    case 1:
        return apply(f, p[0]); // c. p.
    }

    switch (f->type) {
    case type_func:
#ifndef NSHORTCUT
        if (n == f->func.code->args) {
            Value frame[f->func.code->frame];
            frame[0] = f;
            for (index i = 0; i < n; i++)
                frame[1+i] = p[i];
            return run(frame); // c. p.
        }
#endif
        if (n >= f->func.code->args) {
            Value frame[f->func.code->frame];
            frame[0] = f;
            for (index i = 0; i < n; i++)
                frame[1+i] = p[i];
            n -= f->func.code->args;
            p += f->func.code->args;
            hold_array(n, p);
            f = run(frame);
            release_array(1);
            return n ? call(f, n, p) : f; // c. p.
        } else
            return create_proj(f, n, p);
    case type_proj: {
        const Proj* proj = &f->proj;
        index new_n = proj->count;
        Value new_args[add_length(new_n, n)];
        index filled = 0;
        bool partial = 0;
        for (index i = 0; i < proj->count; i++)
            if (proj->args[i] || filled == n)
                partial = partial || !(new_args[i] = proj->args[i]);
            else
                new_args[i] = p[filled++];
        while (filled < n)
            new_args[new_n++] = p[filled++];
        return partial ? project(proj->func, new_n, new_args)
                       :    call(proj->func, new_n, new_args); // c. p.
    }
    case type_comp: {
        // fixme: optimize
        index v = min_valence(f->comp[1]);
        if (n >= v) {
            v = valence(f->comp[1]);
            assert(v > 0);
            Value h = f->comp[0];
            hold(h);
            if (n > v) {
                hold_array(n-v, p+v);
                f = call(f->comp[1], v, p); // c. p. f part, p part
                release(1);
                f = apply(h, f); // c. p. f
                release_array(1);
                return call(f, n-v, p+v); // c. p.
            } else {
                f = call(f->comp[1], n, p); // c. p. f part, p
                release(1);
                f = apply(h, f); // c. p.
                return f;
            }
        } else
            return create_proj(f, n, p);
    }
    case type_verb_prime:
        hold_array(n-1, p+1);
        f = verbs_run[f->verb].unary(p[0]); // c. p. f and p[0]
        release_array(1);
        return call(f, n-1, p+1); // c. p.
    case type_verb:
        if (n == 2)
            return verbs_run[f->verb].binary(p[0], p[1]);
        else
            return verbs_run[f->verb].variadic(n, p);
                   // fixme: spill over instead
    case type_clause:
        if (n == 2)
            return adverbs_run[f->clause.adverb].
                   binary(f->clause.verb, p[0], p[1]);
        else
            return adverbs_run[f->clause.adverb].
                   variadic(f->clause.verb, n, p); // fixme: spill over instead
    default:
        assert(!IS_CALLABLE(f));
        hold_array(n, p); // c. tracks all args here so recurse doesn't have to
        Value r = call_recurse(f, n, p);
        release_array(1);
        return r;
    }
}


Value call_binary(Value f, Value x, Value y) {
    assert(x && y);

    switch (f->type) {
    case type_func: {
        switch (f->func.code->args) {
        case 2: {
            Value frame[f->func.code->frame];
            frame[0] = f;
            frame[1] = x;
            frame[2] = y;
            return run(frame); // c. p.
        }
        case 1: {
            hold(y);
            Value frame[f->func.code->frame];
            frame[0] = f;
            frame[1] = x;
            f = run(frame); // c. p. f and x
            release(1);
            return apply(f, y);
        }
        default:
            assert(f->func.code->args != 0);
            Value p[2] = { x, y };
            return create_proj(f, 2, p);
        }
    }
    case type_proj: {
        const Proj* proj = &f->proj;
        index n = proj->count;
        Value args[add_length(n, 2)];
        index filled = 0;
        bool partial = 0;
        for (index i = 0; i < proj->count; i++)
            if (proj->args[i] || filled == 2)
                partial = partial || !(args[i] = proj->args[i]);
            else
                args[i] = filled++ ? y : x;
        if (filled == 0)
            args[n++] = x;
        if (filled < 2)
            args[n++] = y;
        return partial ? project(proj->func, n, args)
                       :    call(proj->func, n, args); // c. p.
    }
    case type_comp: {
        // fixme: optimize
        Value p[2] = { x, y };
        return call(f, 2, p);
    }
    case type_verb_prime:
        hold(y);
        f = verbs_run[f->verb].unary(x); // c. p. f and x
        release(1);
        return apply(f, y); // c. p. y
    case type_verb:
        return verbs_run[f->verb].binary(x, y); // c. p.
    case type_clause:
        return adverbs_run[f->clause.adverb].binary(f->clause.verb, x, y);
               // c. p.
    default:
        assert(!IS_CALLABLE(f));
        Value p[2] = { x, y };
        hold_array(2, p); // c. tracks all args here so recurse doesn't have to
        Value r = call_recurse(f, 2, p);
        release_array(1);
        return r;
    }
}
