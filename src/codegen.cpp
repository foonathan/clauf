// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <clauf/codegen.hpp>

#include <clauf/ast.hpp>

#include <lauf/asm/builder.h>
#include <lauf/asm/type.h>
#include <lauf/lib/debug.h>
#include <lauf/lib/int.h>
#include <lauf/lib/test.h>
#include <lauf/runtime/builtin.h>
#include <lauf/runtime/value.h>

//=== builtin lauf instructions ===//
namespace
{
LAUF_RUNTIME_BUILTIN(eq_int, 2, 1,
                     LAUF_RUNTIME_BUILTIN_NO_PROCESS | LAUF_RUNTIME_BUILTIN_CONSTANT_FOLD, "eq_int",
                     nullptr)
{
    // Stack: lhs rhs => (lhs == rhs)
    auto lhs = vstack_ptr[1].as_sint;
    auto rhs = vstack_ptr[0].as_sint;

    auto result = lhs == rhs;

    ++vstack_ptr;
    vstack_ptr[0].as_sint = result ? 1 : 0;

    LAUF_RUNTIME_BUILTIN_DISPATCH;
}
} // namespace

//=== codegen ===//
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

    dryad::visit_tree(
        decl->body(),
        [&](const clauf::block_stmt*) {
            // Do nothing, children do all the work.
        },
        [&](dryad::traverse_event ev, const clauf::expr_stmt*) {
            if (ev == dryad::traverse_event::exit)
            {
                // The underlying expression has been visited, and we need to remove its value from
                // the stack.
                lauf_asm_inst_pop(b, 0);
            }
        },
        [&](dryad::traverse_event ev, const clauf::builtin_stmt* stmt) {
            if (ev == dryad::traverse_event::exit)
            {
                // The underlying expression has been visited, and pushed its value onto the stack.
                switch (stmt->builtin())
                {
                case clauf::builtin_stmt::print:
                    // Print the value on top of the stack.
                    lauf_asm_inst_call_builtin(b, lauf_lib_debug_print);
                    // Remove the value after we have printed it.
                    lauf_asm_inst_pop(b, 0);
                    break;
                case clauf::builtin_stmt::assert:
                    // Assert that the value is non-zero.
                    lauf_asm_inst_call_builtin(b, lauf_lib_test_assert);
                    break;
                }
            }
        },
        //=== expression ===//
        [&](const clauf::integer_constant_expr* expr) {
            // Pushes the value of the expression onto the stack.
            lauf_asm_inst_uint(b, expr->value());
        },
        [&](dryad::traverse_event ev, const clauf::binary_expr* expr) {
            if (ev == dryad::traverse_event::exit)
            {
                // At this point, two values have been pushed onto the stack.
                switch (expr->op())
                {
                case clauf::binary_expr::eq:
                    lauf_asm_inst_call_builtin(b, eq_int);
                    break;
                }
            }
        });

    // Add an implicit return 0.
    lauf_asm_inst_uint(b, 0);
    lauf_asm_inst_return(b);

    lauf_asm_build_finish(b);
    return fn;
}
} // namespace

lauf_asm_module* clauf::codegen(const ast& ast)
{
    context ctx(ast);

    for (auto decl : ast.root()->declarations())
        dryad::visit_node(decl, [&](const function_decl* decl) { codegen_function(ctx, decl); });

    return ctx.mod;
}

