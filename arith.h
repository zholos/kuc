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

#ifndef ARITH_H
#define ARITH_H

#include "value.h"

Value plus(Value, Value);
Value minus(Value, Value);
Value times(Value, Value);
Value divide(Value, Value);
Value divide_int(Value, Value);
Value modulo(Value, Value);

Value scalar_plus(Value, Value);
Value scalar_minus(Value, Value);

Value min(Value);
Value max(Value);

Value equal(Value, Value);
Value less(Value, Value);
Value greater(Value, Value);
Value not_equal(Value, Value);
Value not_less(Value, Value);
Value not_greater(Value, Value);

Value neg(Value);
Value not(Value);
Value invert(Value);
Value entier(Value);

Value sum(Value);
Value min(Value);
Value max(Value);
Value primed_sum(Value, Value);
Value primed_min(Value, Value);
Value primed_max(Value, Value);

Value variadic_plus(index n, const Value* p);


#endif /* ARITH_H */
