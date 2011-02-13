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

#include "error.h"

#include "alloc.h"
#include "string.h"
#include "sys.h"
#include "verb.h"

#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>


static struct try_info {
    bool trying;
    jmp_buf jmp;
    Value value;
    struct hold_save_buf hold_save;
    #ifndef NDEBUG
        const char* func;
        const char* file;
        long line;
    #endif
} try;


static void show_error(int handle_parse) {
    Value error = try.value;
    if (!error)
        printf("error\n");
    else {
        index width = 0, marker = 0;
        if (handle_parse >= 0 && IS_MIXED(error) &&
                error->count == 3 &&
               !error->mixed[0]->vector &&
                error->mixed[0]->type == type_name &&
                error->mixed[0]->_name == error_parse->_name &&
               !error->mixed[1]->vector &&
                error->mixed[1]->type == type_index) {
            width = screen_size(NULL);
            if (width)
                marker = (handle_parse + error->mixed[1]->index) % width;
            error = error->mixed[2];
        }
        Value text;
        if (!error->vector && error->type == type_name)
            text = join(create_char('\''), create_stringz(error->_name));
        else
            text = join(create_stringz("error: "), repr(error));

        if (text->count <= width - marker - 4)
            printf("%*s^-- %.*s\n", (int)marker, "",
                                    (int)text->count, text->chars);
        else if (text->count <= marker - 3)
            printf("%*.*s --^\n", (int)(marker - 3),
                                  (int)text->count, text->chars);
        else
            printf("%.*s\n", (int)text->count, text->chars);
    }
#ifndef NDEBUG
    printf("in %s() at %s:%ld\n", try.func, try.file, try.line);
#endif
}


void __attribute__ ((noreturn))
#ifndef NDEBUG
    error_debug(const char* func, const char* file, long line, Value x)
#else
    error(Value x)
#endif
{
    try.value = x;
    #ifndef NDEBUG
        try.func = func;
        try.file = file;
        try.line = line;
    #endif
    if (try.trying)
        longjmp(try.jmp, 1);
    else {
        show_error(-1);
        exit(1);
    }
}


Value protected(Value (*call )(Value), Value arg,
                Value (*catch)(Value,  Value), int handle_parse) {
    struct try_info saved;
    if (try.trying)
        saved = try;
    else {
        saved.trying = 0;
        try.trying = 1;
    }
    hold_save(&try.hold_save);

    Value r;
    if (!setjmp(try.jmp))
        r = call(arg);
    else {
        hold_unroll(&try.hold_save);
        if (catch)
            r = catch(arg, try.value);
        else {
            show_error(handle_parse);
            r = NULL;
        }
    }

    if (saved.trying)
        try = saved;
    else
        try.trying = 0;
    return r;
}
