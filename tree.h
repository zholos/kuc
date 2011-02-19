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

/* This header is included once for each data type with the following macros
   defined:

   TREE_PREFIX - name used in routines: *_insert and *_remove;
                 and in member names:   *_left, *_right, *_balance
   TREE_NODE   - node type (pointer to structure)
   TREE_SAME,
   TREE_LEFT,
   TREE_RIGHT - key comparison functions which take two nodes as arguments
*/

#if !defined(TREE_PREFIX) || !defined(TREE_NODE) || \
    !defined(TREE_SAME) || !defined(TREE_LEFT) || !defined(TREE_RIGHT)
    #error tree.h not configured
#endif


#define PREFIX(name) PREFIX_PASTE(TREE_PREFIX, name)
#define PREFIX_PASTE( prefix, name) PREFIX_PASTE1(prefix, name)
#define PREFIX_PASTE1(prefix, name) prefix##_##name

#define LEFT    PREFIX(left)
#define RIGHT   PREFIX(right)
#define BALANCE PREFIX(balance)

#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define MAX(x, y) ((x) > (y) ? (x) : (y))

static void PREFIX(rotate_left)(TREE_NODE* tree) {
    TREE_NODE child = (*tree)->RIGHT;
    (*tree)->RIGHT = child->LEFT;
    child->LEFT = *tree;
    (*tree)->BALANCE -= MIN(0, child->BALANCE) - 1;
    child->BALANCE += MAX(0, (*tree)->BALANCE) + 1;
    *tree = child;
}


static void PREFIX(rotate_right)(TREE_NODE* tree) {
    TREE_NODE child = (*tree)->LEFT;
    (*tree)->LEFT = child->RIGHT;
    child->RIGHT = *tree;
    (*tree)->BALANCE -= MAX(0, child->BALANCE) + 1;
    child->BALANCE += MIN(0, (*tree)->BALANCE) - 1;
    *tree = child;
}


static bool PREFIX(insert_node)(TREE_NODE* tree, TREE_NODE node) {
    assert(!TREE_SAME(node, *tree));
    if (TREE_LEFT(node, *tree)) {
        if (!(*tree)->LEFT) {
            (*tree)->LEFT = node;
            return ++(*tree)->BALANCE;
        } else if (PREFIX(insert_node)(&(*tree)->LEFT, node)) {
            assert((*tree)->LEFT->BALANCE);
            switch (++(*tree)->BALANCE) {
            case 1:
                return 1;
            case 2:
                if ((*tree)->LEFT->BALANCE < 0)
                    PREFIX(rotate_left)(&(*tree)->LEFT);
                PREFIX(rotate_right)(tree);
                assert(!(*tree)->BALANCE);
            }
        }
    } else {
        if (!(*tree)->RIGHT) {
            (*tree)->RIGHT = node;
            return --(*tree)->BALANCE;
        } else if (PREFIX(insert_node)(&(*tree)->RIGHT, node)) {
            assert((*tree)->RIGHT->BALANCE);
            switch (--(*tree)->BALANCE) {
            case -1:
                return 1;
            case -2:
                if ((*tree)->RIGHT->BALANCE > 0)
                    PREFIX(rotate_right)(&(*tree)->RIGHT);
                PREFIX(rotate_left)(tree);
                assert(!(*tree)->BALANCE);
            }
        }
    }
    return 0;
}


#ifndef TREE_INSERT_ONLY

static void PREFIX(remove_replace)(TREE_NODE* tree, TREE_NODE replace) {
    replace->LEFT    = (*tree)->LEFT;
    replace->RIGHT   = (*tree)->RIGHT;
    replace->BALANCE = (*tree)->BALANCE;
    *tree = replace;
}


static TREE_NODE PREFIX(remove_right)(TREE_NODE* tree, TREE_NODE* node) {
    if ((*tree)->LEFT) {
        TREE_NODE replace = PREFIX(remove_right)(&(*tree)->LEFT, node);
        if (replace) {
            switch (--(*tree)->BALANCE) {
            case 0:
                return replace;
            case -2:
                if ((*tree)->RIGHT->BALANCE > 0)
                    PREFIX(rotate_right)(&(*tree)->RIGHT);
                PREFIX(rotate_left)(tree);
                if (!(*tree)->BALANCE)
                    return replace;
            }
            PREFIX(remove_replace)(node, replace);
        }
        return NULL;
    } else {
        // note: we have saved the pointer to one of the node's children on the
        // stack for updating, so we cannot replace it until we unwind to there
        TREE_NODE replace = *tree;
        *tree = replace->RIGHT;
        return replace;
    }
}


static TREE_NODE PREFIX(remove_left)(TREE_NODE* tree, TREE_NODE* node) {
    if ((*tree)->RIGHT) {
        TREE_NODE replace = PREFIX(remove_left)(&(*tree)->RIGHT, node);
        if (replace) {
            switch (++(*tree)->BALANCE) {
            case 0:
                return replace;
            case 2:
                if ((*tree)->LEFT->BALANCE < 0)
                    PREFIX(rotate_left)(&(*tree)->LEFT);
                PREFIX(rotate_right)(tree);
                if (!(*tree)->BALANCE)
                    return replace;
            }
            PREFIX(remove_replace)(node, replace);
        }
        return NULL;
    } else {
        // see above
        TREE_NODE replace = *tree;
        *tree = replace->LEFT;
        return replace;
    }
}


static bool PREFIX(remove_node)(TREE_NODE* tree, TREE_NODE node) {
    if (*tree == node) {
        if ((*tree)->BALANCE >= 0) {
            if ((*tree)->LEFT) {
                TREE_NODE replace = PREFIX(remove_left)(&(*tree)->LEFT, tree);
                if (replace) {
                    PREFIX(remove_replace)(tree, replace);
                    goto lean_right;
                }
            } else {
                *tree = NULL;
                return 1;
            }
        } else {
            TREE_NODE replace = PREFIX(remove_right)(&(*tree)->RIGHT, tree);
            if (replace) {
                PREFIX(remove_replace)(tree, replace);
                goto lean_left;
            }
        }
    } else if (TREE_LEFT(node, *tree)) {
        if (PREFIX(remove_node)(&(*tree)->LEFT, node))
        lean_right:
            switch (--(*tree)->BALANCE) {
            case 0:
                return 1;
            case -2:
                if ((*tree)->RIGHT->BALANCE > 0)
                    PREFIX(rotate_right)(&(*tree)->RIGHT);
                PREFIX(rotate_left)(tree);
                return !(*tree)->BALANCE;
            }
    } else {
        if (PREFIX(remove_node)(&(*tree)->RIGHT, node))
        lean_left:
            switch (++(*tree)->BALANCE) {
            case 0:
                return 1;
            case 2:
                if ((*tree)->LEFT->BALANCE < 0)
                    PREFIX(rotate_left)(&(*tree)->LEFT);
                PREFIX(rotate_right)(tree);
                return !(*tree)->BALANCE;
            }
    }
    return 0;
}

#endif /* TREE_INSERT_ONLY */


#undef TREE_PREFIX
#undef TREE_NODE
#undef TREE_SAME
#undef TREE_LEFT
#undef TREE_RIGHT
#undef TREE_INSERT_ONLY
