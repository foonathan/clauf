// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <clauf/codegen.hpp>

#include <clauf/ast.hpp>

#include <lauf/asm/builder.h>
#include <lauf/asm/type.h>

namespace
{
struct context
{
    const clauf::ast* ast;
    lauf_asm_module*  mod;
    lauf_asm_builder* builder;

    context(const clauf::ast& ast)
    : ast(&ast), mod(lauf_asm_create_module("main module")),
      builder(lauf_asm_create_builder(lauf_asm_default_build_options))
    {}

    context(const context&)            = delete;
    context& operator=(const context&) = delete;

    ~context()
    {
        lauf_asm_destroy_builder(builder);
    }
};

lauf_asm_function* codegen_function(const context& ctx, const clauf::function_decl* decl)
{
    auto name = decl->name().c_str(ctx.ast->symbols);
    auto fn   = lauf_asm_add_function(ctx.mod, name, {0, 1});

    auto b = ctx.builder;
    lauf_asm_build(b, ctx.mod, fn);

    auto entry = lauf_asm_declare_block(b, {0, 1});
    lauf_asm_build_block(b, entry);

    // STACK: -
    lauf_asm_inst_uint(b, 0);
    // STACK: 0
    lauf_asm_inst_return(b);

    lauf_asm_build_finish(b);
    return fn;
}
} // namespace

lauf_asm_module* clauf::codegen(const ast& ast)
{
    context ctx(ast);

    dryad::visit_tree(ast.tree, [&](const function_decl* decl) { codegen_function(ctx, decl); });

    return ctx.mod;
}

