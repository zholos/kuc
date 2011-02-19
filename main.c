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

#include "alloc.h"
#include "error.h"
#include "func.h"
#include "parse.h"
#include "string.h"
#include "sys.h"
#include "value.h"
#include "verb.h"

#include <ctype.h>
#include <getopt.h>
#include <histedit.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#define index index_hide /* index() should be in string.h anyway */
#include <string.h>
#undef index


static void eval_command(const char* source) {
    protected(eval, create_string(source, strlen(source)), NULL, -1);
}


static void eval_file(const char* filename) {
    Value name = join(create_char(':'),
                      create_string(filename, strlen(filename)));
    name = create_name(name->chars, name->count);
    protected(eval_source, read_file(name), NULL, -1);
}


static const char* interactive_prompt(EditLine* el) {
    return "kuc> ";
}


static bool is_empty(const char* line) {
    for (const char* s = line; *s; ++s)
        if (!isspace(*s))
            return 0;
    return 1;
}


const char* argv0;

void eval_interactive() {
    const char* home = getenv("HOME");
    static const char hist_file[] = "/.kuc_history";
    size_t hist_path_size = home && *home ? strlen(home) + sizeof hist_file : 0;
    char hist_path[hist_path_size];
    if (hist_path_size) {
        strcpy(hist_path, home);
        strcat(hist_path, hist_file);
    }

    EditLine* el = el_init(argv0, stdin, stdout, stderr);
    if (!el)
        assert_failed("el_init");
    el_set(el, EL_PROMPT, interactive_prompt);
    el_set(el, EL_SIGNAL, 1);

    el_set(el, EL_EDITOR, "emacs");
    el_set(el, EL_BIND, "^[[1~", "ed-move-to-beg",      NULL);
    el_set(el, EL_BIND, "^[[2~", "em-toggle-overwrite", NULL);
    el_set(el, EL_BIND, "^[[3~", "ed-delete-next-char", NULL);
    el_set(el, EL_BIND, "^[[4~", "ed-move-to-end",      NULL);
    el_source(el, NULL);

    History* h = history_init();
    if (!h)
        assert_failed("history_init");

    HistEvent e;
    history(h, &e, H_SETSIZE, 1000);
    history(h, &e, H_SETUNIQUE, 1);
    history(h, &e, H_LOAD, hist_path);
    el_set(el, EL_HIST, history, h);

    for (;;) {
        const char* line = el_gets(el, NULL);
        if (!line || !*line) // fixme: can something other than EOF trigger this
            break;
        if (!is_empty(line)) {
            history(h, &e, H_ENTER, line);
            size_t n = strlen(line);
            if (n && line[n-1] == '\n') {
                n--;
                if (n && line[n-1] == '\r')
                    n--;
            }
            Value x = protected(eval, create_string(line, n), NULL, 5);
            if (x && !IS_NULL(x))
                protected(show, x, NULL, -1);
#ifndef NDEBUG
            //dump_heap();
#endif
        }
    }

    history(h, &e, H_SAVE, hist_path);
    history_end(h);
    el_end(el);
}

void help(bool full) {
    if (full)
        puts("kuc 0.0-20110219");
    puts("Usage: kuc [-i | -c command | [-f] file]\n");
}

int main(int argc, char** argv) {
    globals_init();

    argv0 = argv[0];

    int interactive = 1;
    for (;;) {
        int c = getopt(argc, argv, "ic:f:h");
        if (c == -1)
            break;

        switch (c) {
        case 'i':
            if (interactive == 2)
                goto error;
            interactive = 2;
            break;
        case 'c':
            eval_command(optarg);
            if (interactive != 2)
                interactive = 0;
            break;
        case 'f':
            eval_file(optarg);
            if (interactive != 2)
                interactive = 0;
            break;
        case 'h':
            help(1);
            return EXIT_SUCCESS;
        default:
        error:
            help(0);
            return EXIT_FAILURE;
        }
    }

    for (; optind < argc; optind++) {
        eval_file(argv[optind]);
        if (interactive != 2)
            interactive = 0;
    }
    if (interactive)
        if (isatty(STDIN_FILENO))
            eval_interactive();
        else
            eval_file("/dev/stdin");

    // 5.1.2.2.3/1
}
