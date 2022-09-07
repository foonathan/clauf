// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <clauf/codegen.hpp>

#include <cassert>
#include <dryad/node_map.hpp>
#include <lauf/asm/builder.h>
#include <lauf/asm/type.h>
#include <lauf/lib/bits.h>
#include <lauf/lib/debug.h>
#include <lauf/lib/int.h>
#include <lauf/lib/test.h>
#include <lauf/runtime/builtin.h>
#include <lauf/runtime/value.h>
#include <lexy/input_location.hpp>

#include <clauf/assert.hpp>
#include <clauf/ast.hpp>

//=== codegen ===//
namespace
{
struct context
{
    const clauf::ast*                                               ast;
    lauf_asm_module*                                                mod;
    lauf_asm_builder*                                               builder;
    dryad::node_map<const clauf::variable_decl, lauf_asm_global*>   globals;
    dryad::node_map<const clauf::function_decl, lauf_asm_function*> functions;

    context(const clauf::ast& ast)
    : ast(&ast), mod(lauf_asm_create_module("main module")),
      builder(lauf_asm_create_builder(lauf_asm_default_build_options))
    {
        lauf_asm_set_module_debug_path(mod, ast.input.path);
    }

    context(const context&)            = delete;
    context& operator=(const context&) = delete;

    ~context()
    {
        lauf_asm_destroy_builder(builder);
    }
};

template <typename Op>
void call_arithmetic_builtin(lauf_asm_builder* b, Op op)
{
    switch (op)
    {
    case Op::add:
        lauf_asm_inst_call_builtin(b, lauf_lib_int_sadd(LAUF_LIB_INT_OVERFLOW_PANIC));
        break;
    case Op::sub:
        lauf_asm_inst_call_builtin(b, lauf_lib_int_ssub(LAUF_LIB_INT_OVERFLOW_PANIC));
        break;
    case Op::mul:
        lauf_asm_inst_call_builtin(b, lauf_lib_int_smul(LAUF_LIB_INT_OVERFLOW_PANIC));
        break;
    case Op::div:
        lauf_asm_inst_call_builtin(b, lauf_lib_int_sdiv(LAUF_LIB_INT_OVERFLOW_PANIC));
        break;
    case Op::rem:
        lauf_asm_inst_call_builtin(b, lauf_lib_int_srem);
        break;

    case Op::band:
        lauf_asm_inst_call_builtin(b, lauf_lib_bits_and);
        break;
    case Op::bor:
        lauf_asm_inst_call_builtin(b, lauf_lib_bits_or);
        break;
    case Op::bxor:
        lauf_asm_inst_call_builtin(b, lauf_lib_bits_xor);
        break;
    case Op::shl:
        // Overflow wraps around and is not undefined.
        lauf_asm_inst_call_builtin(b, lauf_lib_bits_shl);
        break;
    case Op::shr:
        // implementation-defined behavior: arithmetic right shift
        lauf_asm_inst_call_builtin(b, lauf_lib_bits_sshr);
        break;

    default:
        CLAUF_UNREACHABLE("there aren't any more arithmetic operators in C?!");
        break;
    }
}

lauf_asm_function* codegen_function(context& ctx, const clauf::function_decl* decl)
{
    auto name = decl->name().c_str(ctx.ast->symbols);
    auto fn   = lauf_asm_add_function(ctx.mod, name, {0, 1});
    ctx.functions.insert(decl, fn);

    dryad::node_map<const clauf::decl, lauf_asm_local*> local_vars;

    auto b = ctx.builder;
    lauf_asm_build(b, ctx.mod, fn);

    auto entry = lauf_asm_declare_block(b, 0);
    lauf_asm_build_block(b, entry);

    auto generate_debug_location = [&](const clauf::stmt* stmt) {
        auto location          = ctx.ast->location_of(stmt);
        auto expanded_location = lexy::get_input_location(ctx.ast->input.buffer, location.begin);

        lauf_asm_build_debug_location(b, {std::uint16_t(expanded_location.line_nr()),
                                          std::uint16_t(expanded_location.column_nr()), false});
    };

    dryad::visit_tree(
        decl->body(),
        // We don't need to do any codegen for any types in the tree.
        dryad::ignore_node<clauf::type>,
        //=== statements ===//
        [&](const clauf::block_stmt*) {
            // Do nothing, children do all the work.
        },
        [&](dryad::traverse_event ev, const clauf::expr_stmt* stmt) {
            if (ev == dryad::traverse_event::enter)
                generate_debug_location(stmt);
            else
                // The underlying expression has been visited, and we need to remove its value from
                // the stack.
                lauf_asm_inst_pop(b, 0);
        },
        [&](dryad::traverse_event ev, const clauf::builtin_stmt* stmt) {
            if (ev == dryad::traverse_event::enter)
                generate_debug_location(stmt);
            else
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
        [&](dryad::traverse_event ev, const clauf::return_stmt* stmt) {
            if (ev == dryad::traverse_event::enter)
                generate_debug_location(stmt);
            else
            {
                // The underlying expression has been visited, and we return.
                lauf_asm_inst_return(b);
            }
        },
        //=== declarations ===//
        dryad::ignore_node<clauf::function_decl>,
        [&](const clauf::variable_decl* decl) {
            // TODO: handle types other than int
            auto var = lauf_asm_build_local(b, LAUF_ASM_NATIVE_LAYOUT_OF(lauf_runtime_value));
            local_vars.insert(decl, var);
        },
        //=== expression ===//
        [&](const clauf::integer_constant_expr* expr) {
            // Pushes the value of the expression onto the stack.
            lauf_asm_inst_uint(b, expr->value());
        },
        [&](const clauf::identifier_expr* expr) {
            if (auto var_decl = dryad::node_try_cast<clauf::variable_decl>(expr->declaration()))
            {
                if (auto local_var = local_vars.lookup(var_decl))
                {
                    // Push the value of local_var onto the stack.
                    lauf_asm_inst_local_addr(b, *local_var);
                    lauf_asm_inst_load_field(b, lauf_asm_type_value, 0);
                    return;
                }
                else if (auto global_var = ctx.globals.lookup(var_decl))
                {
                    // Push the value of global_var onto the stack.
                    lauf_asm_inst_global_addr(b, *global_var);
                    lauf_asm_inst_load_field(b, lauf_asm_type_value, 0);
                    return;
                }
            }
            else if (auto fn_decl = dryad::node_try_cast<clauf::function_decl>(expr->declaration()))
            {
                // Push the address of the function onto the stack.
                auto fn = ctx.functions.lookup(fn_decl);
                CLAUF_ASSERT(fn != nullptr, "forgot to populate table");
                lauf_asm_inst_function_addr(b, *fn);
                return;
            }

            CLAUF_UNREACHABLE("currently nothing else supported");
        },
        [&](dryad::traverse_event_exit, const clauf::function_call_expr*) {
            // At this point the address of the function has been pushed onto the stack.
            // Call it, since we don't have any arguments to push.
            lauf_asm_inst_call_indirect(b, {0, 1});
        },
        [&](dryad::traverse_event_exit, const clauf::unary_expr* expr) {
            // At this point, one value has been pushed onto the stack.
            switch (expr->op())
            {
            case clauf::unary_op::plus:
                // Do nothing.
                break;
            case clauf::unary_op::neg:
                lauf_asm_inst_sint(b, -1);
                lauf_asm_inst_call_builtin(b, lauf_lib_int_smul(LAUF_LIB_INT_OVERFLOW_PANIC));
                break;
            case clauf::unary_op::bnot:
                lauf_asm_inst_call_builtin(b, lauf_lib_bits_not);
                break;
            case clauf::unary_op::lnot:
                // If any bit is set, produce 0, otherwise, produce 1.
                lauf_asm_inst_call_builtin(b, lauf_lib_bits_none_set);
                break;
            }
        },
        [&](dryad::traverse_event_exit, const clauf::arithmetic_expr* expr) {
            // At this point, two values have been pushed onto the stack.
            call_arithmetic_builtin(b, expr->op());
        },
        [&](dryad::traverse_event_exit, const clauf::comparison_expr* expr) {
            // At this point, two values have been pushed onto the stack.
            switch (expr->op())
            {
            case clauf::comparison_op::eq:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_EQ);
                break;
            case clauf::comparison_op::ne:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_NE);
                break;
            case clauf::comparison_op::lt:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_LT);
                break;
            case clauf::comparison_op::le:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_LE);
                break;
            case clauf::comparison_op::gt:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_GT);
                break;
            case clauf::comparison_op::ge:
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_GE);
                break;
            }
        },
        [&](dryad::child_visitor<clauf::node_kind> visitor, const clauf::sequenced_expr* expr) {
            switch (expr->op())
            {
            case clauf::sequenced_op::land: {
                auto cur_stack_size     = lauf_asm_build_get_vstack_size(b);
                auto block_eval_right   = lauf_asm_declare_block(b, cur_stack_size);
                auto block_shortcircuit = lauf_asm_declare_block(b, cur_stack_size);
                auto block_end          = lauf_asm_declare_block(b, cur_stack_size + 1);

                visitor(expr->left());
                auto const_target = lauf_asm_inst_branch(b, block_eval_right, block_shortcircuit);

                if (const_target != block_shortcircuit)
                {
                    // We only reach this point if left has been true, so whatever is the result of
                    // right is our result.
                    lauf_asm_build_block(b, block_eval_right);
                    visitor(expr->right());
                    lauf_asm_inst_jump(b, block_end);
                }

                if (const_target != block_eval_right)
                {
                    // We only reach this point if left has been false, so that's the result.
                    lauf_asm_build_block(b, block_shortcircuit);
                    lauf_asm_inst_uint(b, 0);
                    lauf_asm_inst_jump(b, block_end);
                }

                lauf_asm_build_block(b, block_end);
                break;
            }

            case clauf::sequenced_op::lor: {
                auto cur_stack_size     = lauf_asm_build_get_vstack_size(b);
                auto block_eval_right   = lauf_asm_declare_block(b, cur_stack_size);
                auto block_shortcircuit = lauf_asm_declare_block(b, cur_stack_size);
                auto block_end          = lauf_asm_declare_block(b, cur_stack_size + 1);

                visitor(expr->left());
                auto const_target = lauf_asm_inst_branch(b, block_shortcircuit, block_eval_right);

                if (const_target != block_eval_right)
                {
                    // We only reach this point if left has been true, so that's the result.
                    lauf_asm_build_block(b, block_shortcircuit);
                    lauf_asm_inst_uint(b, 1);
                    lauf_asm_inst_jump(b, block_end);
                }

                if (const_target != block_shortcircuit)
                {
                    // We only reach this point if left has been false, so whatever is the result of
                    // right is our result.
                    lauf_asm_build_block(b, block_eval_right);
                    visitor(expr->right());
                    lauf_asm_inst_jump(b, block_end);
                }

                lauf_asm_build_block(b, block_end);
                break;
            }

            case clauf::sequenced_op::comma:
                visitor(expr->left());
                lauf_asm_inst_pop(b, 0);
                visitor(expr->right());
                break;
            }
        },
        [&](dryad::child_visitor<clauf::node_kind> visitor, const clauf::assignment_expr* expr) {
            // Evaluate and push the rvalue.
            visitor(expr->right());

            if (expr->op() != clauf::assignment_op::none)
            {
                // Push the value of the lvalue onto the stack.
                visitor(expr->left());

                // Perform the operation, swapping the values.
                lauf_asm_inst_roll(b, 1);
                call_arithmetic_builtin(b, expr->op());
            }

            // The stack now contains the value we're assigning.
            // Duplicate it, as we want to leave it on the stack as the result of the expression.
            lauf_asm_inst_pick(b, 0);

            // Push the address of the lvalue onto the stack.
            // TODO: only identifier_expr is an lvalue at the moment
            dryad::visit_node_all(expr->left(), [&](const clauf::identifier_expr* expr) {
                if (auto var_decl = dryad::node_try_cast<clauf::variable_decl>(expr->declaration()))
                {
                    if (auto local_var = local_vars.lookup(var_decl))
                    {
                        // Push the value of local_var onto the stack.
                        lauf_asm_inst_local_addr(b, *local_var);
                        return;
                    }
                    else if (auto global_var = ctx.globals.lookup(var_decl))
                    {
                        // Push the value of global_var onto the stack.
                        lauf_asm_inst_global_addr(b, *global_var);
                        return;
                    }
                }

                CLAUF_UNREACHABLE("we don't support anything else yet");
            });
            // Store the value into address.
            lauf_asm_inst_store_field(b, lauf_asm_type_value, 0);
        },
        [&](dryad::child_visitor<clauf::node_kind> visitor, const clauf::conditional_expr* expr) {
            auto cur_stack_size = lauf_asm_build_get_vstack_size(b);
            auto block_if_true  = lauf_asm_declare_block(b, cur_stack_size);
            auto block_if_false = lauf_asm_declare_block(b, cur_stack_size);
            auto block_end      = lauf_asm_declare_block(b, cur_stack_size + 1);

            // Evaluate the condition and push it onto the stack.
            visitor(expr->condition());
            auto const_target = lauf_asm_inst_branch(b, block_if_true, block_if_false);

            if (const_target != block_if_false)
            {
                // Evaluate the if_true case.
                lauf_asm_build_block(b, block_if_true);
                visitor(expr->if_true());
                lauf_asm_inst_jump(b, block_end);
            }

            if (const_target != block_if_true)
            {
                // Evaluate the if_false case.
                lauf_asm_build_block(b, block_if_false);
                visitor(expr->if_false());
                lauf_asm_inst_jump(b, block_end);
            }

            // Continue, but in the new block.
            lauf_asm_build_block(b, block_end);
        });

    // Add an implicit return 0.
    lauf_asm_build_debug_location(b, {0, 0, true});
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
        dryad::visit_node(
            decl, [&](const function_decl* decl) { codegen_function(ctx, decl); },
            [&](const variable_decl* decl) {
                // TODO: types other than int
                auto global
                    = lauf_asm_add_global_zero_data(ctx.mod,
                                                    LAUF_ASM_NATIVE_LAYOUT_OF(lauf_runtime_value));
                lauf_asm_set_global_debug_name(ctx.mod, global,
                                               decl->name().c_str(ctx.ast->symbols));
                ctx.globals.insert(decl, global);
            });

    return ctx.mod;
}

