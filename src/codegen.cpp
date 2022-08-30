// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <clauf/codegen.hpp>

#include <clauf/ast.hpp>

#include <lauf/asm/builder.h>
#include <lauf/asm/type.h>
#include <lauf/lib/bits.h>
#include <lauf/lib/debug.h>
#include <lauf/lib/int.h>
#include <lauf/lib/test.h>
#include <lauf/runtime/builtin.h>
#include <lauf/runtime/value.h>

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

    auto entry = lauf_asm_declare_block(b, 0);
    lauf_asm_build_block(b, entry);

    dryad::visit_tree(
        decl->body(),
        // We don't need to do any codegen for any types in the tree.
        dryad::ignore_node<clauf::type>,
        //=== statements ===//
        [&](const clauf::block_stmt*) {
            // Do nothing, children do all the work.
        },
        [&](dryad::traverse_event_exit, const clauf::expr_stmt*) {
            // The underlying expression has been visited, and we need to remove its value from
            // the stack.
            lauf_asm_inst_pop(b, 0);
        },
        [&](dryad::traverse_event_exit, const clauf::builtin_stmt* stmt) {
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
        },
        //=== expression ===//
        [&](const clauf::integer_constant_expr* expr) {
            // Pushes the value of the expression onto the stack.
            lauf_asm_inst_uint(b, expr->value());
        },
        [&](dryad::traverse_event_exit, const clauf::unary_expr* expr) {
            // At this point, one value has been pushed onto the stack.
            switch (expr->op())
            {
            case clauf::unary_expr::plus:
                // Do nothing.
                break;
            case clauf::unary_expr::neg:
                lauf_asm_inst_sint(b, -1);
                lauf_asm_inst_call_builtin(b, lauf_lib_int_smul(LAUF_LIB_INT_OVERFLOW_PANIC));
                break;
            case clauf::unary_expr::bnot:
                lauf_asm_inst_call_builtin(b, lauf_lib_bits_not);
                break;
            case clauf::unary_expr::lnot:
                // If any bit is set, produce 0, otherwise, produce 1.
                lauf_asm_inst_call_builtin(b, lauf_lib_bits_none_set);
                break;
            }
        },
        [&](dryad::traverse_event_exit, const clauf::binary_expr* expr) {
            // At this point, two values have been pushed onto the stack.
            switch (expr->op())
            {
            case clauf::binary_expr::add:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_sadd(LAUF_LIB_INT_OVERFLOW_PANIC));
                break;
            case clauf::binary_expr::sub:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_ssub(LAUF_LIB_INT_OVERFLOW_PANIC));
                break;
            case clauf::binary_expr::mul:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_smul(LAUF_LIB_INT_OVERFLOW_PANIC));
                break;
            case clauf::binary_expr::div:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_sdiv(LAUF_LIB_INT_OVERFLOW_PANIC));
                break;
            case clauf::binary_expr::rem:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_srem);
                break;

            case clauf::binary_expr::band:
                lauf_asm_inst_call_builtin(b, lauf_lib_bits_and);
                break;
            case clauf::binary_expr::bor:
                lauf_asm_inst_call_builtin(b, lauf_lib_bits_or);
                break;
            case clauf::binary_expr::bxor:
                lauf_asm_inst_call_builtin(b, lauf_lib_bits_xor);
                break;
            case clauf::binary_expr::shl:
                // Overflow wraps around and is not undefined.
                lauf_asm_inst_call_builtin(b, lauf_lib_bits_shl);
                break;
            case clauf::binary_expr::shr:
                // implementation-defined behavior: arithmetic right shift
                lauf_asm_inst_call_builtin(b, lauf_lib_bits_sshr);
                break;

            case clauf::binary_expr::eq:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_EQ);
                break;
            case clauf::binary_expr::ne:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_NE);
                break;
            case clauf::binary_expr::lt:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_LT);
                break;
            case clauf::binary_expr::le:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_LE);
                break;
            case clauf::binary_expr::gt:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_GT);
                break;
            case clauf::binary_expr::ge:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_GE);
                break;
            }
        },
        [&](dryad::child_visitor<clauf::node_kind> visitor,
            const clauf::sequenced_binary_expr*    expr) {
            switch (expr->op())
            {
            case clauf::sequenced_binary_expr::land: {
                auto cur_stack_size     = lauf_asm_build_get_vstack_size(b);
                auto block_eval_right   = lauf_asm_declare_block(b, cur_stack_size);
                auto block_shortcircuit = lauf_asm_declare_block(b, cur_stack_size);
                auto block_end          = lauf_asm_declare_block(b, cur_stack_size + 1);

                visitor(expr->left());
                lauf_asm_inst_branch2(b, block_eval_right, block_shortcircuit);

                // We only reach this point if left has been true, so whatever is the result of
                // right is our result.
                lauf_asm_build_block(b, block_eval_right);
                visitor(expr->right());
                lauf_asm_inst_jump(b, block_end);

                // We only reach this point if left has been false, so that's the result.
                lauf_asm_build_block(b, block_shortcircuit);
                lauf_asm_inst_uint(b, 0);
                lauf_asm_inst_jump(b, block_end);

                lauf_asm_build_block(b, block_end);
                break;
            }

            case clauf::sequenced_binary_expr::lor: {
                auto cur_stack_size     = lauf_asm_build_get_vstack_size(b);
                auto block_eval_right   = lauf_asm_declare_block(b, cur_stack_size);
                auto block_shortcircuit = lauf_asm_declare_block(b, cur_stack_size);
                auto block_end          = lauf_asm_declare_block(b, cur_stack_size + 1);

                visitor(expr->left());
                lauf_asm_inst_branch2(b, block_shortcircuit, block_eval_right);

                // We only reach this point if left has been true, so that's the result.
                lauf_asm_build_block(b, block_shortcircuit);
                lauf_asm_inst_uint(b, 1);
                lauf_asm_inst_jump(b, block_end);

                // We only reach this point if left has been false, so whatever is the result of
                // right is our result.
                lauf_asm_build_block(b, block_eval_right);
                visitor(expr->right());
                lauf_asm_inst_jump(b, block_end);

                lauf_asm_build_block(b, block_end);
                break;
            }

            case clauf::sequenced_binary_expr::comma:
                visitor(expr->left());
                lauf_asm_inst_pop(b, 0);
                visitor(expr->right());
                break;
            }
        },
        [&](dryad::child_visitor<clauf::node_kind> visitor, const clauf::conditional_expr* expr) {
            auto cur_stack_size = lauf_asm_build_get_vstack_size(b);
            auto block_if_true  = lauf_asm_declare_block(b, cur_stack_size);
            auto block_if_false = lauf_asm_declare_block(b, cur_stack_size);
            auto block_end      = lauf_asm_declare_block(b, cur_stack_size + 1);

            // Evaluate the condition and push it onto the stack.
            visitor(expr->condition());
            lauf_asm_inst_branch2(b, block_if_true, block_if_false);

            // Evaluate the if_true case.
            lauf_asm_build_block(b, block_if_true);
            visitor(expr->if_true());
            lauf_asm_inst_jump(b, block_end);

            // Evaluate the if_false case.
            lauf_asm_build_block(b, block_if_false);
            visitor(expr->if_false());
            lauf_asm_inst_jump(b, block_end);

            // Continue, but in the new block.
            lauf_asm_build_block(b, block_end);
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

