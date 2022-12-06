// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#ifndef CLAUF_COMPILER_HPP_INCLUDED
#define CLAUF_COMPILER_HPP_INCLUDED

#include <clauf/ast.hpp>
#include <lauf/asm/module.h>
#include <lexy/input/buffer.hpp>
#include <optional>

struct lauf_vm;

namespace clauf
{
struct compilation_result
{
    clauf::ast       ast;
    lauf_asm_module* mod;
};

/// If input is well-formed C (including name lookup and type checking), return its AST.
/// Otherwise, log error and return nothing.
std::optional<compilation_result> compile(lauf_vm* vm, file&& input);
} // namespace clauf

#endif // CLAUF_COMPILER_HPP_INCLUDED

