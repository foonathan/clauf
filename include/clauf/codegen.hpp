// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#ifndef CLAUF_CODEGEN_HPP_INCLUDED
#define CLAUF_CODEGEN_HPP_INCLUDED

#include <lauf/asm/module.h>
#include <lauf/vm.h>
#include <vector>

namespace clauf
{
struct ast;
class expr;

lauf_asm_module* codegen(lauf_vm* vm, const ast& ast);
} // namespace clauf

#endif // CLAUF_CODEGEN_HPP_INCLUDED

