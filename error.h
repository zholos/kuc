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

#ifndef ERROR_H
#define ERROR_H

#include "value.h"

#ifndef NDEBUG
    #define error(x) error_debug(__func__, __FILE__, __LINE__, x)
    void error_debug(const char*, const char*, long, Value)
       __attribute__ ((noreturn, cold));
#else
    void error(Value) __attribute__ ((noreturn, cold));
#endif

Value protected(Value (*call )(Value), Value,
                Value (*catch)(Value,  Value), int);

#endif /* ERROR_H */
