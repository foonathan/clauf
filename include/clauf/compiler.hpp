// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#ifndef CLAUF_COMPILER_HPP_INCLUDED
#define CLAUF_COMPILER_HPP_INCLUDED

#include <lexy/input/buffer.hpp>
#include <optional>

namespace clauf
{
struct ast;

using buffer = lexy::buffer<lexy::utf8_char_encoding>;

/// If input is well-formed C (including name lookup and type checking), return its AST.
/// Otherwise, log error and return nothing.
std::optional<ast> compile(const buffer& input);
} // namespace clauf

#endif // CLAUF_COMPILER_HPP_INCLUDED

