// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#ifndef CLAUF_CODEGEN_HPP_INCLUDED
#define CLAUF_CODEGEN_HPP_INCLUDED

#include <lauf/asm/module.h>

namespace clauf
{
struct ast;

lauf_asm_module* codegen(const ast& ast);
} // namespace clauf

#endif // CLAUF_CODEGEN_HPP_INCLUDED

