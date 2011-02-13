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

#ifndef CODE_H
#define CODE_H

#include "value.h"

#include <stdint.h>

typedef uint_least16_t instr_word;
#define INSTR_BITS 16
#define INSTR_PART (1 << (INSTR_BITS-2))
#define INSTR_LAST (4 * (INSTR_PART - 1) + 3)

#if !defined(NJIT) && !defined(__amd64__)
#define NJIT
#endif

typedef struct code {
    index args, frame, closed;
    const instr_word* instr;
    Value* literals;
#ifndef NJIT
    Value (*jit)(Value*);
#endif
}* Code; // fixme: Code typedef is temporary


Code code(index args, index frame, index closed,
          const instr_word* instr, Value* literals);
#ifndef NJIT
void code_finalize(Code);
#endif

#ifndef NJIT
static inline Value run(Value* frame) {
    return frame[0]->func.code->jit(frame);
}
#else
Value run(Value* frame);
#endif


#endif /* CODE_H */
