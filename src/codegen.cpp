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
#include <vector>

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
    dryad::node_map<const clauf::decl, lauf_asm_local*>             local_vars;
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

lauf_asm_type codegen_type(const clauf::type* ty)
{
    return dryad::visit_node_all(
        ty,
        [](const clauf::builtin_type* ty) {
            switch (ty->type_kind())
            {
            case clauf::builtin_type::void_:
                CLAUF_UNREACHABLE("not needed in lauf");

            case clauf::builtin_type::sint8:
                return lauf_lib_int_s8;
            case clauf::builtin_type::uint8:
                return lauf_lib_int_u8;
            case clauf::builtin_type::sint16:
                return lauf_lib_int_s16;
            case clauf::builtin_type::uint16:
                return lauf_lib_int_u16;
            case clauf::builtin_type::sint32:
                return lauf_lib_int_s32;
            case clauf::builtin_type::uint32:
                return lauf_lib_int_u32;
            case clauf::builtin_type::sint64:
                return lauf_lib_int_s64;
            case clauf::builtin_type::uint64:
                return lauf_lib_int_u64;
            }
        },
        [](const clauf::pointer_type*) { return lauf_asm_type_value; },
        [](const clauf::function_type*) {
            CLAUF_UNREACHABLE("not the type of a variable");
            return lauf_asm_type_value;
        });
}

template <typename Op>
void call_arithmetic_builtin(lauf_asm_builder* b, Op op, const clauf::type* ty)
{
    switch (op)
    {
    case Op::add:
        if (clauf::is_signed_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_sadd(LAUF_LIB_INT_OVERFLOW_PANIC));
        else if (clauf::is_unsigned_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_uadd(LAUF_LIB_INT_OVERFLOW_WRAP));
        else
            CLAUF_UNREACHABLE("invalid type");
        break;
    case Op::sub:
        if (clauf::is_signed_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_ssub(LAUF_LIB_INT_OVERFLOW_PANIC));
        else if (clauf::is_unsigned_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_usub(LAUF_LIB_INT_OVERFLOW_WRAP));
        else
            CLAUF_UNREACHABLE("invalid type");
        break;
    case Op::mul:
        if (clauf::is_signed_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_smul(LAUF_LIB_INT_OVERFLOW_PANIC));
        else if (clauf::is_unsigned_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_umul(LAUF_LIB_INT_OVERFLOW_WRAP));
        else
            CLAUF_UNREACHABLE("invalid type");
        break;
    case Op::div:
        if (clauf::is_signed_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_sdiv(LAUF_LIB_INT_OVERFLOW_PANIC));
        else if (clauf::is_unsigned_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_udiv);
        else
            CLAUF_UNREACHABLE("invalid type");
        break;
    case Op::rem:
        if (clauf::is_signed_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_srem);
        else if (clauf::is_unsigned_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_urem);
        else
            CLAUF_UNREACHABLE("invalid type");
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
        if (clauf::is_signed_int(ty))
            // implementation-defined behavior: arithmetic right shift
            lauf_asm_inst_call_builtin(b, lauf_lib_bits_sshr);
        else if (clauf::is_unsigned_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_bits_ushr);
        else
            CLAUF_UNREACHABLE("invalid type");
        break;

    default:
        CLAUF_UNREACHABLE("there aren't any more arithmetic operators in C?!");
        break;
    }
}

// Evalutes the expression as an lvalue and returns its type.
lauf_asm_type codegen_lvalue(context& ctx, const clauf::expr* expr)
{
    auto b    = ctx.builder;
    auto type = lauf_asm_type_value;
    dryad::visit_node_all(expr, [&](const clauf::identifier_expr* expr) {
        if (auto var_decl = dryad::node_try_cast<clauf::variable_decl>(expr->declaration()))
        {
            type = codegen_type(var_decl->type());
            if (auto local_var = ctx.local_vars.lookup(var_decl))
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
        else if (auto param_decl = dryad::node_try_cast<clauf::parameter_decl>(expr->declaration()))
        {
            type = codegen_type(param_decl->type());
            if (auto local_var = ctx.local_vars.lookup(param_decl))
            {
                // Push the address of the parameter onto the stack.
                lauf_asm_inst_local_addr(b, *local_var);
                return;
            }
        }

        CLAUF_UNREACHABLE("we don't support anything else yet");
    });
    return type;
}

lauf_asm_function* codegen_function(context& ctx, const clauf::function_decl* decl)
{
    std::vector<const clauf::parameter_decl*> params;
    for (auto param : decl->parameters())
        params.push_back(param);
    auto parameter_count = params.size();

    auto return_count = clauf::is_void(decl->type()->return_type()) ? 0 : 1;

    auto name = decl->name().c_str(ctx.ast->symbols);
    auto fn   = lauf_asm_add_function(ctx.mod, name,
                                      {static_cast<std::uint8_t>(parameter_count),
                                       static_cast<std::uint8_t>(return_count)});
    ctx.functions.insert(decl, fn);

    ctx.local_vars = {};

    auto b = ctx.builder;
    lauf_asm_build(b, ctx.mod, fn);

    auto entry = lauf_asm_declare_block(b, static_cast<std::uint8_t>(parameter_count));
    lauf_asm_build_block(b, entry);

    // We create variables for all parameters and store the value into them.
    // Since parameters have been pushed onto the stack and are thus popped in reverse,
    // we need to iterate in reverse order.
    for (auto iter = params.rbegin(); iter != params.rend(); ++iter)
    {
        auto type = codegen_type((*iter)->type());
        auto var  = lauf_asm_build_local(b, type.layout);
        ctx.local_vars.insert(*iter, var);

        lauf_asm_inst_local_addr(b, var);
        lauf_asm_inst_store_field(b, type, 0);
    }

    lauf_asm_block* block_loop_end    = nullptr;
    lauf_asm_block* block_loop_header = nullptr;
    dryad::visit_tree(
        decl->body(),
        //=== statements ===//
        [&, anchor = lexy::input_location_anchor(ctx.ast->input.buffer)] //
        (dryad::traverse_event_enter, const clauf::stmt* stmt) mutable {
            // Generate debug location for all instructions generated by a statement.
            auto location = ctx.ast->location_of(stmt);
            auto expanded_location
                = lexy::get_input_location(ctx.ast->input.buffer, location.begin, anchor);

            lauf_asm_build_debug_location(b, {std::uint16_t(expanded_location.line_nr()),
                                              std::uint16_t(expanded_location.column_nr()), false});

            anchor = expanded_location.anchor();
        },
        [&](dryad::traverse_event_exit, const clauf::expr_stmt*) {
            // The underlying expression has been visited, and we need to remove its value from
            // the stack -- if the expression did not do that for us already.
            if (lauf_asm_build_get_vstack_size(b) == 1)
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
        [&](dryad::traverse_event_exit, const clauf::return_stmt*) {
            // The underlying expression has been visited, and we return.
            lauf_asm_inst_return(b);
        },
        [&](const clauf::break_stmt*) {
            CLAUF_ASSERT(block_loop_end != nullptr, "break statement outside of loop");
            lauf_asm_inst_jump(b, block_loop_end);
        },
        [&](const clauf::continue_stmt*) {
            CLAUF_ASSERT(block_loop_header != nullptr, "continue statement outside of loop");
            lauf_asm_inst_jump(b, block_loop_header);
        },
        [&](dryad::child_visitor<clauf::node_kind> visitor, const clauf::if_stmt* stmt) {
            auto block_if_true  = lauf_asm_declare_block(b, 0);
            auto block_if_false = lauf_asm_declare_block(b, 0);
            auto block_end      = lauf_asm_declare_block(b, 0);

            // Evaluate the condition.
            visitor(stmt->condition());
            // Now 0/1 is on top of the stack.
            // Branch to one of the basic blocks.
            auto const_target = lauf_asm_inst_branch(b, block_if_true, block_if_false);

            if (const_target != block_if_false)
            {
                // Evaluate the then statement.
                lauf_asm_build_block(b, block_if_true);
                visitor(stmt->then());
                lauf_asm_inst_jump(b, block_end);
            }

            if (const_target != block_if_true)
            {
                // Evaluate the else statement.
                lauf_asm_build_block(b, block_if_false);
                if (stmt->has_else())
                    visitor(stmt->else_());
                lauf_asm_inst_jump(b, block_end);
            }

            // Continue, but in the new block.
            lauf_asm_build_block(b, block_end);
        },
        [&](dryad::child_visitor<clauf::node_kind> visitor, const clauf::while_stmt* stmt) {
            // loop_header:
            //      evaluate condition
            //      branch to loop_end or loop_body
            // loop_body:
            //      evaluate body
            //      jump to loop_header
            // loop_end:
            //      continue with rest of the program

            auto prev_loop_header = block_loop_header;
            auto prev_loop_end    = block_loop_end;

            block_loop_header    = lauf_asm_declare_block(b, 0);
            auto block_loop_body = lauf_asm_declare_block(b, 0);
            block_loop_end       = lauf_asm_declare_block(b, 0);

            switch (stmt->loop_kind())
            {
            case clauf::while_stmt::loop_while:
                // For a while loop we need to check the loop header first.
                lauf_asm_inst_jump(b, block_loop_header);
                break;
            case clauf::while_stmt::loop_do_while:
                // For a do while loop we need to execute the body once first.
                lauf_asm_inst_jump(b, block_loop_body);
            }

            // Evaluate condition in loop header and branch.
            lauf_asm_build_block(b, block_loop_header);
            visitor(stmt->condition());
            lauf_asm_inst_branch(b, block_loop_body, block_loop_end);

            // Evaluate body.
            lauf_asm_build_block(b, block_loop_body);
            visitor(stmt->body());
            lauf_asm_inst_jump(b, block_loop_header);

            // Continue on with the rest.
            lauf_asm_build_block(b, block_loop_end);
            block_loop_header = prev_loop_header;
            block_loop_end    = prev_loop_end;
        },
        //=== declarations ===//
        dryad::ignore_node<clauf::function_decl>,
        [&](dryad::traverse_event_exit, const clauf::variable_decl* decl) {
            auto type = codegen_type(decl->type());
            auto var  = lauf_asm_build_local(b, type.layout);
            ctx.local_vars.insert(decl, var);

            if (decl->has_initializer())
            {
                // If we have an initializer, it has been visited already and its value pushed on
                // top of the stack. Store the initial value in the local variable.
                lauf_asm_inst_local_addr(b, var);
                lauf_asm_inst_store_field(b, type, 0);
            }
        },
        //=== expression ===//
        [&](const clauf::integer_constant_expr* expr) {
            // Pushes the value of the expression onto the stack.
            lauf_asm_inst_uint(b, expr->value());
        },
        [&](const clauf::identifier_expr* expr) {
            if (auto var_decl = dryad::node_try_cast<clauf::variable_decl>(expr->declaration()))
            {
                auto ty = codegen_type(var_decl->type());
                if (auto local_var = ctx.local_vars.lookup(var_decl))
                {
                    // Push the value of local_var onto the stack.
                    lauf_asm_inst_local_addr(b, *local_var);
                    lauf_asm_inst_load_field(b, ty, 0);
                    return;
                }
                else if (auto global_var = ctx.globals.lookup(var_decl))
                {
                    // Push the value of global_var onto the stack.
                    lauf_asm_inst_global_addr(b, *global_var);
                    lauf_asm_inst_load_field(b, ty, 0);
                    return;
                }
            }
            else if (auto param_decl
                     = dryad::node_try_cast<clauf::parameter_decl>(expr->declaration()))
            {
                auto ty = codegen_type(param_decl->type());
                if (auto local_var = ctx.local_vars.lookup(param_decl))
                {
                    // Push the value of the parameter onto the stack.
                    lauf_asm_inst_local_addr(b, *local_var);
                    lauf_asm_inst_load_field(b, ty, 0);
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
        [&](dryad::child_visitor<clauf::node_kind> visitor, const clauf::function_call_expr* expr) {
            // Push each argument onto the stack.
            for (auto argument : expr->arguments())
                visitor(argument);

            // Push the address of the function onto the stack.
            visitor(expr->function());

            // Call the function.
            auto type = dryad::node_cast<clauf::function_type>(expr->function()->type());
            auto argument_count
                = std::distance(type->parameters().begin(), type->parameters().end());
            auto return_count = clauf::is_void(type->return_type()) ? 0 : 1;
            lauf_asm_inst_call_indirect(b,
                                        {std::uint8_t(argument_count), std::uint8_t(return_count)});
        },
        [&](dryad::traverse_event_exit, const clauf::cast_expr* expr) {
            // At this point, the value to be casted is on top of the stack.
            if (clauf::is_void(expr->type()))
            {
                // Discard the value.
                lauf_asm_inst_pop(b, 0);
            }
            else if (clauf::is_unsigned_int(expr->type()))
            {
                if (clauf::is_signed_int(expr->child()->type()))
                    lauf_asm_inst_call_builtin(b, lauf_lib_int_stou(LAUF_LIB_INT_OVERFLOW_WRAP));
                else
                    // If it is also unsigned, then we don't need to do any conversion or overflow
                    // checking. All stack values are 64 bit anyway, so we will never need to cast
                    // between them.
                    CLAUF_PRECONDITION(clauf::is_unsigned_int(expr->child()->type()));
            }
            else if (clauf::is_signed_int(expr->type()))
            {
                if (clauf::is_unsigned_int(expr->child()->type()))
                {
                    lauf_asm_inst_call_builtin(b, lauf_lib_int_utos(LAUF_LIB_INT_OVERFLOW_PANIC));
                }
                else
                {
                    CLAUF_PRECONDITION(clauf::is_signed_int(expr->child()->type()));
                    // Just check for overflow.
                    auto target_rank = clauf::integer_rank_of(expr->type());
                    auto source_rank = clauf::integer_rank_of(expr->child()->type());
                    if (target_rank < source_rank)
                    {
                        // Check that the value fits in the target.
                        // This pushes 0/1 onto the stack.
                        switch (target_rank)
                        {
                        case 8:
                            lauf_asm_inst_call_builtin(b, lauf_lib_int_s8_overflow);
                            break;
                        case 16:
                            lauf_asm_inst_call_builtin(b, lauf_lib_int_s16_overflow);
                            break;
                        case 32:
                            lauf_asm_inst_call_builtin(b, lauf_lib_int_s32_overflow);
                            break;
                        case 64:
                            lauf_asm_inst_call_builtin(b, lauf_lib_int_s64_overflow);
                            break;

                        default:
                            CLAUF_UNREACHABLE("forgot to add size");
                        }

                        // Panic on overflow.
                        auto msg = lauf_asm_build_string_literal(b, "integer overflow");
                        lauf_asm_inst_global_addr(b, msg);
                        lauf_asm_inst_panic_if(b);
                    }
                }
            }
            else if (clauf::is_pointer(expr->type()) && clauf::is_pointer(expr->child()->type()))
            {
                // We don't need to do anything, pointers in lauf aren't typed.
            }
            else
            {
                CLAUF_UNREACHABLE("no other conversion is allowed");
            }
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
                // NOT is XOR with -1 (all bits set)
                lauf_asm_inst_sint(b, -1);
                lauf_asm_inst_call_builtin(b, lauf_lib_bits_xor);
                break;
            case clauf::unary_op::lnot:
                // If any bit is set, produce 0, otherwise, produce 1.
                lauf_asm_inst_uint(b, 0);
                lauf_asm_inst_call_builtin(b, lauf_lib_int_ucmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_EQ);
                break;

            case clauf::unary_op::pre_inc:
            case clauf::unary_op::pre_dec: {
                // Add/subtract one to the current value.
                lauf_asm_inst_uint(b, 1);
                call_arithmetic_builtin(b,
                                        expr->op() == clauf::unary_op::pre_inc
                                            ? clauf::arithmetic_op::add
                                            : clauf::arithmetic_op::sub,
                                        expr->type());

                // Save a copy into the lvalue.
                lauf_asm_inst_pick(b, 0);
                auto type = codegen_lvalue(ctx, expr->child());
                lauf_asm_inst_store_field(b, type, 0);

                // At this point, the new value is on the stack.
                break;
            }

            case clauf::unary_op::post_inc:
            case clauf::unary_op::post_dec: {
                // We duplicate the old value as we want to evaluate that.
                lauf_asm_inst_pick(b, 0);

                // Add/subtract one to the current value.
                lauf_asm_inst_uint(b, 1);
                call_arithmetic_builtin(b,
                                        expr->op() == clauf::unary_op::post_inc
                                            ? clauf::arithmetic_op::add
                                            : clauf::arithmetic_op::sub,
                                        expr->type());

                // Store the new value in the lvalue, this removes it from the stack.
                auto type = codegen_lvalue(ctx, expr->child());
                lauf_asm_inst_store_field(b, type, 0);

                // At this point, the old value is on the stack.
                break;
            }

            case clauf::unary_op::address:
                // Remove the value of the child expression and push its address instead.
                lauf_asm_inst_pop(b, 0);
                codegen_lvalue(ctx, expr->child());
                break;
            }
        },
        [&](dryad::traverse_event_exit, const clauf::arithmetic_expr* expr) {
            // At this point, two values have been pushed onto the stack.
            call_arithmetic_builtin(b, expr->op(), expr->type());
        },
        [&](dryad::traverse_event_exit, const clauf::comparison_expr* expr) {
            // At this point, two values have been pushed onto the stack.
            // Compare them.
            if (clauf::is_signed_int(expr->left()->type()))
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
            else if (clauf::is_unsigned_int(expr->left()->type()))
                lauf_asm_inst_call_builtin(b, lauf_lib_int_ucmp);
            else
                CLAUF_UNREACHABLE("invalid type");

            // And convert the three-way result into 0/1.
            switch (expr->op())
            {
            case clauf::comparison_op::eq:
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_EQ);
                break;
            case clauf::comparison_op::ne:
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_NE);
                break;
            case clauf::comparison_op::lt:
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_LT);
                break;
            case clauf::comparison_op::le:
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_LE);
                break;
            case clauf::comparison_op::gt:
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_GT);
                break;
            case clauf::comparison_op::ge:
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
            // Push the value we're assigning.
            // This might involve an arithmetic operation.
            if (expr->op() != clauf::assignment_op::none)
            {
                visitor(expr->left());
                visitor(expr->right());
                call_arithmetic_builtin(b, expr->op(), expr->type());
            }
            else
            {
                visitor(expr->right());
            }

            // The stack now contains the value we're assigning.
            // If the expression is not used in an expression statement, we need the value, so
            // duplicate it.
            if (!dryad::node_has_kind<clauf::expr_stmt>(expr->parent()))
            {
                lauf_asm_inst_pick(b, 0);
            }

            // Push the address of the lvalue onto the stack.
            auto type = codegen_lvalue(ctx, expr->left());
            // Store the value into address.
            lauf_asm_inst_store_field(b, type, 0);
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

    lauf_asm_build_debug_location(b, {0, 0, true});
    if (return_count > 0)
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
        dryad::visit_node(
            decl, [&](const function_decl* decl) { codegen_function(ctx, decl); },
            [&](const variable_decl* decl) {
                if (decl->has_initializer())
                    CLAUF_TODO("initializers for global variables not yet supported");

                // TODO: types other than int
                auto global
                    = lauf_asm_add_global_zero_data(ctx.mod, codegen_type(decl->type()).layout);
                lauf_asm_set_global_debug_name(ctx.mod, global,
                                               decl->name().c_str(ctx.ast->symbols));
                ctx.globals.insert(decl, global);
            });

    return ctx.mod;
}

