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

#ifndef APPLY_H
#define APPLY_H

#include "value.h"

Value items(Value x, Value y);
Value apply(Value f, Value x);
Value modify_item(index n, const Value* p);
Value modify_element(index n, const Value* p);

Value assign_item(index n, const Value* p);
Value assign_element(index n, const Value* p);

index valence(Value x); // INDEX_MAX for variadic
index min_valence(Value x);

Value project(Value f, index n, const Value* args);
Value project_unary(Value f, Value x);
Value call(Value f, index n, const Value* args);
Value call_binary(Value f, Value x, Value y);


#endif /* APPLY_H */
