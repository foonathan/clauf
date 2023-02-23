// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <clauf/codegen.hpp>

#include <cassert>
#include <dlfcn.h>
#include <dryad/node_map.hpp>
#include <ffi.h>
#include <lauf/asm/builder.h>
#include <lauf/asm/program.h>
#include <lauf/asm/type.h>
#include <lauf/lib/bits.h>
#include <lauf/lib/debug.h>
#include <lauf/lib/heap.h>
#include <lauf/lib/int.h>
#include <lauf/lib/memory.h>
#include <lauf/lib/test.h>
#include <lauf/runtime/builtin.h>
#include <lauf/runtime/memory.h>
#include <lauf/runtime/process.h>
#include <lauf/runtime/value.h>
#include <lexy/input_location.hpp>
#include <stdexcept>
#include <vector>

#include <clauf/assert.hpp>
#include <clauf/ast.hpp>
#include <clauf/diagnostic.hpp>

//=== helper functions ===//
namespace
{
const lauf_asm_type* codegen_lauf_type(const clauf::type* ty)
{
    return dryad::visit_node_all(
        ty,
        [](const clauf::builtin_type* ty) -> const lauf_asm_type* {
            switch (ty->type_kind())
            {
            case clauf::builtin_type::void_:
                return nullptr;
            case clauf::builtin_type::nullptr_t:
                return &lauf_asm_type_value;

            case clauf::builtin_type::sint8:
                return &lauf_lib_int_s8;
            case clauf::builtin_type::uint8:
            case clauf::builtin_type::char_:
                return &lauf_lib_int_u8;
            case clauf::builtin_type::sint16:
                return &lauf_lib_int_s16;
            case clauf::builtin_type::uint16:
                return &lauf_lib_int_u16;
            case clauf::builtin_type::sint32:
                return &lauf_lib_int_s32;
            case clauf::builtin_type::uint32:
                return &lauf_lib_int_u32;
            case clauf::builtin_type::sint64:
                return &lauf_lib_int_s64;
            case clauf::builtin_type::uint64:
                return &lauf_lib_int_u64;
            }
        },
        [](const clauf::pointer_type*) { return &lauf_asm_type_value; },
        [](const clauf::array_type*) { return nullptr; },
        [](const clauf::function_type*) { return nullptr; },
        [](const clauf::qualified_type* ty) { return codegen_lauf_type(ty->unqualified_type()); },
        [](const clauf::decl_type*) {
            // TODO: we assume it is always a struct
            return nullptr;
        });
}

/// A first class type can be pushed onto the vstack and manipulated by lauf directly.
/// Otherwise, we need to use pointers and manipulate it indirectly.
bool is_first_class_type(const clauf::type* ty)
{
    return codegen_lauf_type(ty) != nullptr;
}

// INVARIANT: the resulting layout has a size that is a multiple of alignment.
lauf_asm_layout codegen_lauf_layout(const clauf::type* ty)
{
    if (auto array_ty = dryad::node_try_cast<clauf::array_type>(ty))
    {
        auto element_layout = codegen_lauf_layout(array_ty->element_type());
        return lauf_asm_array_layout(element_layout, array_ty->size());
    }
    else if (auto decl_ty = dryad::node_try_cast<clauf::decl_type>(ty))
    {
        auto decl = dryad::node_cast<clauf::struct_decl>(decl_ty->decl()->definition());

        std::vector<lauf_asm_layout> members;
        for (auto member : decl->members())
            members.push_back(codegen_lauf_layout(member->type()));

        return lauf_asm_aggregate_layout(members.data(), members.size());
    }
    else
    {
        return codegen_lauf_type(ty)->layout;
    }
}

ffi_type* codegen_ffi_type(const clauf::type* ty)
{
    return dryad::visit_node_all(
        ty,
        [](const clauf::builtin_type* ty) {
            switch (ty->type_kind())
            {
            case clauf::builtin_type::void_:
                return &ffi_type_void;
            case clauf::builtin_type::nullptr_t:
                return &ffi_type_pointer;

            case clauf::builtin_type::sint8:
                return &ffi_type_sint8;
            case clauf::builtin_type::uint8:
            case clauf::builtin_type::char_:
                return &ffi_type_uint8;
            case clauf::builtin_type::sint16:
                return &ffi_type_sint16;
            case clauf::builtin_type::uint16:
                return &ffi_type_uint16;
            case clauf::builtin_type::sint32:
                return &ffi_type_sint32;
            case clauf::builtin_type::uint32:
                return &ffi_type_uint32;
            case clauf::builtin_type::sint64:
                return &ffi_type_sint64;
            case clauf::builtin_type::uint64:
                return &ffi_type_uint64;
            }
        },
        [](const clauf::pointer_type*) { return &ffi_type_pointer; },
        [](const clauf::array_type*) -> ffi_type* {
            CLAUF_UNREACHABLE("array cannot be passed as function parameter");
            return nullptr;
        },
        [](const clauf::function_type*) -> ffi_type* {
            CLAUF_UNREACHABLE("function cannot be passed as function parameter");
            return nullptr;
        },
        [](const clauf::qualified_type* ty) { return codegen_ffi_type(ty->unqualified_type()); });
}

template <typename Op, typename Expr>
void call_arithmetic_builtin(lauf_asm_builder* b, Op op, const Expr* expr)
{
    if constexpr (std::is_same_v<Expr, clauf::arithmetic_expr>)
    {
        if (op == Op::ptrdiff)
        {
            // Get the difference in bytes.
            lauf_asm_inst_call_builtin(b, lauf_lib_memory_addr_distance);

            // Convert that to the type of the pointee.
            auto pointee_type = codegen_lauf_type(
                dryad::node_cast<clauf::pointer_type>(expr->left()->type())->pointee_type());
            lauf_asm_inst_uint(b, pointee_type->layout.size);
            lauf_asm_inst_call_builtin(b, lauf_lib_int_sdiv(LAUF_LIB_INT_OVERFLOW_PANIC));

            return;
        }
    }

    auto ty = expr->type();
    switch (op)
    {
    case Op::add:
        if (clauf::is_signed_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_sadd(LAUF_LIB_INT_OVERFLOW_PANIC));
        else if (clauf::is_unsigned_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_uadd(LAUF_LIB_INT_OVERFLOW_WRAP));
        else if (clauf::is_pointer(ty))
        {
            // The offset is on top of the stack, as we normalized the expr.
            // Multiply it by the size of the type.
            auto pointee_type
                = codegen_lauf_layout(dryad::node_cast<clauf::pointer_type>(ty)->pointee_type());
            lauf_asm_inst_uint(b, pointee_type.size);
            lauf_asm_inst_call_builtin(b, lauf_lib_int_smul(LAUF_LIB_INT_OVERFLOW_PANIC));

            // Offset the pointer.
            auto addr_add = lauf_lib_memory_addr_add(LAUF_LIB_MEMORY_ADDR_OVERFLOW_PANIC);
            lauf_asm_inst_call_builtin(b, addr_add);
        }
        else
            CLAUF_UNREACHABLE("invalid type");
        break;
    case Op::sub:
        if (clauf::is_signed_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_ssub(LAUF_LIB_INT_OVERFLOW_PANIC));
        else if (clauf::is_unsigned_int(ty))
            lauf_asm_inst_call_builtin(b, lauf_lib_int_usub(LAUF_LIB_INT_OVERFLOW_WRAP));
        else if (clauf::is_pointer(ty))
        {
            // The offset is on top of the stack, as we normalized the expr.
            // Multiply it by the size of the type.
            auto pointee_type
                = codegen_lauf_layout(dryad::node_cast<clauf::pointer_type>(ty)->pointee_type());
            lauf_asm_inst_uint(b, pointee_type.size);
            lauf_asm_inst_call_builtin(b, lauf_lib_int_smul(LAUF_LIB_INT_OVERFLOW_PANIC));

            // Offset the pointer.
            auto addr_sub = lauf_lib_memory_addr_sub(LAUF_LIB_MEMORY_ADDR_OVERFLOW_PANIC);
            lauf_asm_inst_call_builtin(b, addr_sub);
        }
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

void* argument_ptrs[32];

// This builtin takes two arguments:
// * vstack_ptr[0] is the native address of the ffi_function
// * vstack_ptr[1] is an address to an array of pointers to the actual arguments
// * vstack_ptr[2] is an address to store the return value into
LAUF_RUNTIME_BUILTIN(call_native, 3, 0, LAUF_RUNTIME_BUILTIN_DEFAULT, "call_native", nullptr)
{
    auto ffi_function           = static_cast<clauf::ffi_function*>(vstack_ptr[0].as_native_ptr);
    auto argument_array_address = vstack_ptr[1].as_address;
    auto return_address         = vstack_ptr[2].as_address;

    CLAUF_ASSERT(ffi_function->cif.nargs < 32, "too many arguments");
    auto argument_addresses = static_cast<lauf_runtime_value*>(
        lauf_runtime_get_mut_ptr(process, argument_array_address, {1, 1}));
    for (auto i = 0u; i != ffi_function->cif.nargs; ++i)
        argument_ptrs[i]
            = lauf_runtime_get_mut_ptr(process, argument_addresses[i].as_address, {1, 1});

    ffi_call(&ffi_function->cif, reinterpret_cast<void (*)()>(ffi_function->addr),
             lauf_runtime_get_mut_ptr(process, return_address, {1, 1}), argument_ptrs);

    vstack_ptr += 3;
    LAUF_RUNTIME_BUILTIN_DISPATCH;
}

// Translates a lauf address into the native pointer representation.
// It takes one argument, which is the address, and returns one argument, which is the pointer.
LAUF_RUNTIME_BUILTIN(translate_address_to_pointer, 1, 1, LAUF_RUNTIME_BUILTIN_DEFAULT,
                     "translate_address_to_pointer", &call_native)
{
    auto address = vstack_ptr[0].as_address;

    auto ptr = lauf_runtime_get_const_ptr(process, address, {0, 1});
    if (ptr == nullptr)
        return lauf_runtime_panic(process, "invalid address");
    vstack_ptr[0].as_native_ptr = (void*)ptr;

    LAUF_RUNTIME_BUILTIN_DISPATCH;
}
// As above, but translates to a C string.
LAUF_RUNTIME_BUILTIN(translate_address_to_string, 1, 1, LAUF_RUNTIME_BUILTIN_DEFAULT,
                     "translate_address_to_string", &translate_address_to_pointer)
{
    auto address = vstack_ptr[0].as_address;

    auto ptr = lauf_runtime_get_cstr(process, address);
    if (ptr == nullptr)
        return lauf_runtime_panic(process, "invalid address");
    vstack_ptr[0].as_native_ptr = (void*)ptr;

    LAUF_RUNTIME_BUILTIN_DISPATCH;
}

// Translates a native pointer back to a lauf address.
LAUF_RUNTIME_BUILTIN(translate_pointer_to_address, 1, 1, LAUF_RUNTIME_BUILTIN_DEFAULT,
                     "translate_pointer_to_address", &translate_address_to_string)
{
    auto ptr = vstack_ptr[0].as_native_ptr;

    auto address             = lauf_runtime_add_static_mut_allocation(process, ptr, size_t(-1));
    vstack_ptr[0].as_address = address;

    LAUF_RUNTIME_BUILTIN_DISPATCH;
}
LAUF_RUNTIME_BUILTIN(translate_string_to_address, 1, 1, LAUF_RUNTIME_BUILTIN_DEFAULT,
                     "translate_string_to_address", &translate_pointer_to_address)
{
    auto ptr = static_cast<char*>(vstack_ptr[0].as_native_ptr);

    auto address = lauf_runtime_add_static_mut_allocation(process, ptr, std::strlen(ptr) + 1);
    vstack_ptr[0].as_address = address;

    LAUF_RUNTIME_BUILTIN_DISPATCH;
}

struct context
{
    lauf_vm*                                                               vm;
    clauf::diagnostic_logger*                                              logger;
    const clauf::ast_symbol_interner*                                      symbols;
    const clauf::file*                                                     input;
    lauf_asm_module*                                                       mod;
    lauf_asm_chunk*                                                        consteval_chunk;
    lauf_asm_global*                                                       consteval_result_global;
    lauf_asm_builder*                                                      chunk_builder;
    lauf_asm_builder*                                                      body_builder;
    const dryad::node_map<const clauf::variable_decl, lauf_asm_global*>*   globals;
    const dryad::node_map<const clauf::function_decl, lauf_asm_function*>* functions;

    dryad::node_map<const clauf::decl, lauf_asm_local*> local_vars;
};

enum class codegen_expr_mode
{
    // Evaluates the expression and result in the address; only applicable for actual lvalues or
    // decayed expressions of pointer type.
    address,
    // Evaluates the expression and stores it in the address on top of the vstack.
    store,
    // Evaluates the expression and pushes it on top of the vstack.
    value,
    // Evaluates the expression and discards its result; doesn't put anything onto the vstack.
    discard,
};

void codegen_expr(context& ctx, lauf_asm_builder* b, const clauf::expr* expr,
                  codegen_expr_mode mode);

void codegen_constant(context&, lauf_asm_builder* b, const clauf::expr* expr,
                      codegen_expr_mode mode)
{
    if (mode == codegen_expr_mode::discard)
        return;

    // Evaluate the expression and put its value on top of the vstack.
    dryad::visit_node_all(
        expr,
        [&](const clauf::nullptr_constant_expr*) {
            // Push null address onto the stack.
            lauf_asm_inst_null(b);
        },
        [&](const clauf::integer_constant_expr* expr) {
            // Pushes the value of the expression onto the stack.
            lauf_asm_inst_uint(b, expr->value());
        },
        [&](const clauf::string_literal_expr* expr) {
            // Get the address of the global that contains the string literal.
            auto str = lauf_asm_build_string_literal(b, expr->value());
            lauf_asm_inst_global_addr(b, str);
        },
        [&](const clauf::type_constant_expr* expr) {
            auto layout = codegen_lauf_layout(expr->operand_type());
            switch (expr->op())
            {
            case clauf::type_constant_expr::sizeof_:
                lauf_asm_inst_uint(b, layout.size);
                break;
            case clauf::type_constant_expr::alignof_:
                lauf_asm_inst_uint(b, layout.alignment);
                break;
            }
        });

    // Process the value according to mode.
    switch (mode)
    {
    case codegen_expr_mode::address:
        // This is only possible if the expression is a string literal,
        // and it pushed its address earlier, so we don't need to do anything.
        CLAUF_PRECONDITION(dryad::node_has_kind<clauf::string_literal_expr>(expr));
        break;

    case codegen_expr_mode::store:
        // vstack looks like: addr value
        lauf_asm_inst_roll(b, 1);
        lauf_asm_inst_store_field(b, *codegen_lauf_type(expr->type()), 0);
        break;

    case codegen_expr_mode::value:
        // Value is already on the vstack, do nothing.
        break;

    case codegen_expr_mode::discard:
        CLAUF_UNREACHABLE("handled above");
        break;
    }
}

void codegen_identifier_as_lvalue(context& ctx, lauf_asm_builder* b,
                                  const clauf::identifier_expr* expr)
{
    if (auto var_decl = dryad::node_try_cast<clauf::variable_decl>(expr->declaration()))
    {
        if (auto local_var = ctx.local_vars.lookup(var_decl))
        {
            // Push the value of local_var onto the stack.
            lauf_asm_inst_local_addr(b, *local_var);
            return;
        }
        else if (auto global_var = ctx.globals->lookup(var_decl->definition()))
        {
            // Push the value of global_var onto the stack.
            lauf_asm_inst_global_addr(b, *global_var);
            return;
        }
    }
    else if (auto param_decl = dryad::node_try_cast<clauf::parameter_decl>(expr->declaration()))
    {
        if (auto local_var = ctx.local_vars.lookup(param_decl))
        {
            // Push the address of the parameter onto the stack.
            lauf_asm_inst_local_addr(b, *local_var);
            return;
        }
    }
    else if (auto fn_decl = dryad::node_try_cast<clauf::function_decl>(expr->declaration()))
    {
        // Push the address of the function onto the stack.
        auto fn = fn_decl->linkage() == clauf::linkage::native
                      ? ctx.functions->lookup(fn_decl)
                      : ctx.functions->lookup(fn_decl->definition());
        CLAUF_ASSERT(fn != nullptr, "forgot to populate table");
        lauf_asm_inst_function_addr(b, *fn);
        return;
    }
}

void codegen_member_as_lvalue(context& ctx, lauf_asm_builder* b,
                              const clauf::member_access_expr* expr)
{
    codegen_expr(ctx, b, expr->object(), codegen_expr_mode::address);

    std::vector<lauf_asm_layout> members;
    for (auto member :
         dryad::node_cast<clauf::struct_decl>(expr->object_type_definition())->members())
    {
        members.push_back(codegen_lauf_layout(member->type()));
        if (member->name() == expr->member_name())
            break;
    }

    lauf_asm_inst_aggregate_member(b, members.size() - 1, members.data(), members.size());
}

void codegen_expr(context& ctx, lauf_asm_builder* b, const clauf::expr* expr,
                  codegen_expr_mode mode)
{
    auto process_mode = [&](bool top_is_lvalue) {
        if (clauf::is_void(expr->type()))
        {
            CLAUF_ASSERT(mode == codegen_expr_mode::discard, "what else would you do with void");
            // Nothing is put on top of the vstack for void.
            return;
        }

        switch (mode)
        {
        case codegen_expr_mode::address:
            // It is already an lvalue, no need to do anything.
            break;

        case codegen_expr_mode::store:
            // The vstack looks like this: address value
            // Need to store value in address.
            if (auto type = codegen_lauf_type(expr->type()))
            {
                lauf_asm_inst_roll(b, 1);
                lauf_asm_inst_store_field(b, *type, 0);
            }
            else
            {
                // value is actually a pointer to the object since it's not first class here.
                lauf_asm_inst_uint(b, codegen_lauf_layout(expr->type()).size);
                lauf_asm_inst_call_builtin(b, lauf_lib_memory_copy);
            }
            break;
        case codegen_expr_mode::value:
            if (top_is_lvalue)
            {
                if (auto type = codegen_lauf_type(expr->type()))
                    lauf_asm_inst_load_field(b, *type, 0);
            }
            break;
        case codegen_expr_mode::discard:
            lauf_asm_inst_pop(b, 0);
            break;
        }
    };

    dryad::visit_node_all(
        expr,
        [&](const clauf::nullptr_constant_expr* expr) { codegen_constant(ctx, b, expr, mode); },
        [&](const clauf::integer_constant_expr* expr) { codegen_constant(ctx, b, expr, mode); },
        [&](const clauf::string_literal_expr* expr) { codegen_constant(ctx, b, expr, mode); },
        [&](const clauf::type_constant_expr* expr) { codegen_constant(ctx, b, expr, mode); },
        [&](const clauf::builtin_expr* expr) {
            // Get the value of the argument.
            codegen_expr(ctx, b, expr->expr(), codegen_expr_mode::value);

            switch (expr->builtin())
            {
            case clauf::builtin_expr::print:
                // Print the value on top of the stack.
                lauf_asm_inst_call_builtin(b, lauf_lib_debug_print);
                // Remove the value after we have printed it.
                lauf_asm_inst_pop(b, 0);
                break;
            case clauf::builtin_expr::assert:
                // Assert that the value is non-zero.
                lauf_asm_inst_call_builtin(b, lauf_lib_test_assert);
                break;

            case clauf::builtin_expr::malloc:
                // Add the alignment parameter.
                lauf_asm_inst_uint(b, 8);
                // Move size argument which is below alignment to the top.
                lauf_asm_inst_roll(b, 1);
                // Allocate memory.
                lauf_asm_inst_call_builtin(b, lauf_lib_heap_alloc);
                break;
            case clauf::builtin_expr::free:
                // Call free with the address on top of the stack.
                lauf_asm_inst_call_builtin(b, lauf_lib_heap_free);
                break;
            }

            process_mode(false);
        },
        [&](const clauf::identifier_expr* expr) {
            switch (mode)
            {
            case codegen_expr_mode::address:
                codegen_identifier_as_lvalue(ctx, b, expr);
                break;

            case codegen_expr_mode::store:
                codegen_identifier_as_lvalue(ctx, b, expr);
                lauf_asm_inst_uint(b, codegen_lauf_layout(expr->type()).size);
                lauf_asm_inst_call_builtin(b, lauf_lib_memory_copy);
                break;

            case codegen_expr_mode::value:
                codegen_identifier_as_lvalue(ctx, b, expr);
                if (auto type = codegen_lauf_type(expr->type()))
                    lauf_asm_inst_load_field(b, *type, 0);
                break;

            case codegen_expr_mode::discard:
                // No need to evaluate anything.
                break;
            }
        },
        [&](const clauf::member_access_expr* expr) {
            switch (mode)
            {
            case codegen_expr_mode::address:
                codegen_member_as_lvalue(ctx, b, expr);
                break;

            case codegen_expr_mode::store:
                codegen_member_as_lvalue(ctx, b, expr);
                lauf_asm_inst_uint(b, codegen_lauf_layout(expr->type()).size);
                lauf_asm_inst_call_builtin(b, lauf_lib_memory_copy);
                break;

            case codegen_expr_mode::value:
                codegen_member_as_lvalue(ctx, b, expr);
                if (auto type = codegen_lauf_type(expr->type()))
                    lauf_asm_inst_load_field(b, *type, 0);
                break;

            case codegen_expr_mode::discard:
                // Evaluate and discard the object.
                codegen_expr(ctx, b, expr->object(), codegen_expr_mode::discard);
                break;
            }
        },
        [&](const clauf::function_call_expr* expr) {
            CLAUF_PRECONDITION(mode != codegen_expr_mode::address);

            auto type = dryad::node_cast<clauf::function_type>(expr->function()->type());
            auto argument_count
                = std::distance(type->parameters().begin(), type->parameters().end());
            auto return_count = clauf::is_void(type->return_type()) ? 0 : 1;

            auto function_requires_return_ptr
                = !clauf::is_void(type->return_type()) && !is_first_class_type(type->return_type());
            if (function_requires_return_ptr)
            {
                // We're dealing with a return type that is not first-class,
                // so we need to push a pointer to store the result into.

                if (mode == codegen_expr_mode::store)
                {
                    // We have an address on top of the vstack anyway,
                    // where we want to store the result into.
                    // So we don't need to do anything.
                }
                else
                {
                    // Generate space to store the result into.
                    auto call_result
                        = lauf_asm_build_local(b, codegen_lauf_layout(type->return_type()));
                    lauf_asm_inst_local_addr(b, call_result);
                }

                ++argument_count;
            }

            // Push each argument onto the stack.
            for (auto argument : expr->arguments())
                codegen_expr(ctx, b, argument, codegen_expr_mode::value);

            // Push the address of the function onto the stack.
            codegen_expr(ctx, b, expr->function(), codegen_expr_mode::address);

            // Call the function.
            lauf_asm_inst_call_indirect(b,
                                        {std::uint8_t(argument_count), std::uint8_t(return_count)});

            if (function_requires_return_ptr
                && (mode == codegen_expr_mode::discard || mode == codegen_expr_mode::store))
                // We have the return ptr again on top of the vstack, and need to discard it.
                lauf_asm_inst_pop(b, 0);
        },
        [&](const clauf::cast_expr* expr) {
            // Get the value of the thing we're casting.
            codegen_expr(ctx, b, expr->child(),
                         clauf::is_void(expr->type()) ? codegen_expr_mode::discard
                                                      : codegen_expr_mode::value);

            if (clauf::is_void(expr->type()))
            { // NOLINT: for clarity
              // Value has been discarded already.
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
            else if (clauf::is_pointer(expr->type()) && clauf::is_nullptr_constant(expr->child()))
            {
                // We don't want the value of the child expression.
                // This is because the integer 0 does not have the same representation as the null
                // address.
                lauf_asm_inst_pop(b, 0);
                // Push null instead.
                lauf_asm_inst_null(b);
            }
            else
            {
                CLAUF_UNREACHABLE("no other conversion is allowed");
            }

            process_mode(false);
        },
        [&](const clauf::decay_expr* expr) {
            if (mode == codegen_expr_mode::address)
                mode = codegen_expr_mode::value;
            codegen_expr(ctx, b, expr->child(), mode);
        },
        [&](const clauf::unary_expr* expr) {
            switch (expr->op())
            {
            case clauf::unary_op::plus:
                codegen_expr(ctx, b, expr->child(), codegen_expr_mode::value);
                break;
            case clauf::unary_op::neg:
                codegen_expr(ctx, b, expr->child(), codegen_expr_mode::value);
                lauf_asm_inst_sint(b, -1);
                lauf_asm_inst_call_builtin(b, lauf_lib_int_smul(LAUF_LIB_INT_OVERFLOW_PANIC));
                break;
            case clauf::unary_op::bnot:
                codegen_expr(ctx, b, expr->child(), codegen_expr_mode::value);
                // NOT is XOR with -1 (all bits set)
                lauf_asm_inst_sint(b, -1);
                lauf_asm_inst_call_builtin(b, lauf_lib_bits_xor);
                break;
            case clauf::unary_op::lnot:
                codegen_expr(ctx, b, expr->child(), codegen_expr_mode::value);
                // If any bit is set, produce 0, otherwise, produce 1.
                lauf_asm_inst_uint(b, 0);
                lauf_asm_inst_call_builtin(b, lauf_lib_int_ucmp);
                lauf_asm_inst_cc(b, LAUF_ASM_INST_CC_EQ);
                break;

            case clauf::unary_op::pre_inc:
            case clauf::unary_op::pre_dec: {
                auto type = codegen_lauf_type(expr->type());

                // Get the address on top of the vstack.
                codegen_expr(ctx, b, expr->child(), codegen_expr_mode::address);

                // Do a load to get the value.
                lauf_asm_inst_pick(b, 0);
                lauf_asm_inst_load_field(b, *type, 0);

                // Add/subtract one to the current value.
                lauf_asm_inst_uint(b, 1);
                call_arithmetic_builtin(b,
                                        expr->op() == clauf::unary_op::pre_inc
                                            ? clauf::arithmetic_op::add
                                            : clauf::arithmetic_op::sub,
                                        expr);

                // vstack looks like this: address new_value
                // First duplicate new_value as that is the result: address new_value new_value
                lauf_asm_inst_pick(b, 0);
                // Move the address on top of the vstack.
                lauf_asm_inst_roll(b, 2);
                lauf_asm_inst_store_field(b, *type, 0);

                // At this point, the new value is on the stack.
                break;
            }

            case clauf::unary_op::post_inc:
            case clauf::unary_op::post_dec: {
                auto type = codegen_lauf_type(expr->type());

                // Get the address on top of the vstack.
                codegen_expr(ctx, b, expr->child(), codegen_expr_mode::address);

                // Do a load to get the value.
                lauf_asm_inst_pick(b, 0);
                lauf_asm_inst_load_field(b, *type, 0);

                // We duplicate the old value as we want to evaluate that.
                lauf_asm_inst_pick(b, 0);

                // Add/subtract one to the ccrrent value.
                lauf_asm_inst_uint(b, 1);
                call_arithmetic_builtin(b,
                                        expr->op() == clauf::unary_op::post_inc
                                            ? clauf::arithmetic_op::add
                                            : clauf::arithmetic_op::sub,
                                        expr);

                // vstack looks like this: address old_value new_value
                // Store new_value into address
                lauf_asm_inst_roll(b, 2);
                lauf_asm_inst_store_field(b, *type, 0);

                // At this point, the old value is on the stack.
                break;
            }

            case clauf::unary_op::deref:
            case clauf::unary_op::address:
                // Evaluate it as an address.
                codegen_expr(ctx, b, expr->child(), codegen_expr_mode::address);
                break;
            }

            process_mode(clauf::is_lvalue(expr));
        },
        [&](const clauf::arithmetic_expr* expr) {
            codegen_expr(ctx, b, expr->left(), codegen_expr_mode::value);
            codegen_expr(ctx, b, expr->right(), codegen_expr_mode::value);
            call_arithmetic_builtin(b, expr->op(), expr);
            process_mode(false);
        },
        [&](const clauf::comparison_expr* expr) {
            codegen_expr(ctx, b, expr->left(), codegen_expr_mode::value);
            codegen_expr(ctx, b, expr->right(), codegen_expr_mode::value);

            // Compare them.
            if (clauf::is_signed_int(expr->left()->type()))
            {
                lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
            }
            else if (clauf::is_unsigned_int(expr->left()->type()))
            {
                lauf_asm_inst_call_builtin(b, lauf_lib_int_ucmp); // NOLINT
            }
            else if (clauf::is_pointer(expr->left()->type())
                     || clauf::is_pointer(expr->right()->type())
                     || clauf::is_nullptr_constant(expr->left())
                     || clauf::is_nullptr_constant(expr->right()))
            {
                if (expr->op() == clauf::comparison_op::eq
                    || expr->op() == clauf::comparison_op::ne)
                {
                    // We're comparing pointers like integers for equality.
                    // This does a bitwise comparison of the address.
                    // Since two addresses are bitwise equal iff both point to the same object,
                    // this works.
                    lauf_asm_inst_call_builtin(b, lauf_lib_int_ucmp);
                }
                else
                {
                    // We need to check that they belong to the same allocation before allowing a
                    // comparison.
                    // This is done by getting the distance between the pointers, which panics if
                    // they're not part of the same allocation.
                    lauf_asm_inst_call_builtin(b, lauf_lib_memory_addr_distance);
                    // And now we're comparing the distance with 0.
                    lauf_asm_inst_uint(b, 0);
                    lauf_asm_inst_call_builtin(b, lauf_lib_int_scmp);
                }
            }
            else
            {
                CLAUF_UNREACHABLE("invalid type");
            }

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

            process_mode(false);
        },
        [&](const clauf::sequenced_expr* expr) {
            switch (expr->op())
            {
            case clauf::sequenced_op::land: {
                auto cur_stack_size     = lauf_asm_build_get_vstack_size(b);
                auto block_eval_right   = lauf_asm_declare_block(b, cur_stack_size);
                auto block_shortcircuit = lauf_asm_declare_block(b, cur_stack_size);
                auto block_end          = lauf_asm_declare_block(b, cur_stack_size + 1);

                codegen_expr(ctx, b, expr->left(), codegen_expr_mode::value);
                auto const_target = lauf_asm_inst_branch(b, block_eval_right, block_shortcircuit);

                if (const_target != block_shortcircuit)
                {
                    // We only reach this point if left has been true, so whatever is the result of
                    // right is our result.
                    lauf_asm_build_block(b, block_eval_right);
                    codegen_expr(ctx, b, expr->right(), codegen_expr_mode::value);
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

                codegen_expr(ctx, b, expr->left(), codegen_expr_mode::value);
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
                    codegen_expr(ctx, b, expr->right(), codegen_expr_mode::value);
                    lauf_asm_inst_jump(b, block_end);
                }

                lauf_asm_build_block(b, block_end);
                break;
            }

            case clauf::sequenced_op::comma:
                codegen_expr(ctx, b, expr->left(), codegen_expr_mode::value);
                lauf_asm_inst_pop(b, 0);
                codegen_expr(ctx, b, expr->right(), codegen_expr_mode::value);
                break;
            }

            process_mode(false);
        },
        [&](const clauf::assignment_expr* expr) {
            CLAUF_PRECONDITION(mode != codegen_expr_mode::address);

            // Get the address of the left hand side.
            codegen_expr(ctx, b, expr->left(), codegen_expr_mode::address);
            // Since the result of assignment is the value of the left-hand side, we might need it
            // again.
            lauf_asm_inst_pick(b, 0);

            if (expr->op() != clauf::assignment_op::none)
            {
                CLAUF_ASSERT(clauf::is_lvalue(expr->left()), "lhs of assignment should be lvalue");

                // Load the value of the left hand side.
                lauf_asm_inst_pick(b, 0);
                auto type = codegen_lauf_type(expr->left()->type());
                lauf_asm_inst_load_field(b, *type, 0);

                // Evaluate the right hand side.
                codegen_expr(ctx, b, expr->right(), codegen_expr_mode::value);
                // And combine the two.
                call_arithmetic_builtin(b, expr->op(), expr);

                // Manually store result.
                lauf_asm_inst_roll(b, 1);
                lauf_asm_inst_store_field(b, *type, 0);
            }
            else
            {
                // Evaluate the right hand side and store it into the adress on top of the vstack.
                codegen_expr(ctx, b, expr->right(), codegen_expr_mode::store);
            }

            switch (mode)
            {
            case codegen_expr_mode::address:
                CLAUF_UNREACHABLE("precondition failure");
                break;

            case codegen_expr_mode::store:
                // vstack looks as follows: store_address left_address
                // Memcpy left_address into store_address.
                lauf_asm_inst_uint(b, codegen_lauf_layout(expr->type()).size);
                lauf_asm_inst_call_builtin(b, lauf_lib_memory_copy);
                break;

            case codegen_expr_mode::value:
                // We have the left_address on top of the vstack.
                // Load it, if it's a first class type.
                if (auto type = codegen_lauf_type(expr->type()))
                    lauf_asm_inst_load_field(b, *type, 0);
                break;

            case codegen_expr_mode::discard:
                // We have the left_address on top of the vstack.
                // Discard it.
                lauf_asm_inst_pop(b, 0);
                break;
            }
        },
        [&](const clauf::conditional_expr* expr) {
            auto cur_stack_size = lauf_asm_build_get_vstack_size(b);
            auto block_if_true  = lauf_asm_declare_block(b, cur_stack_size);
            auto block_if_false = lauf_asm_declare_block(b, cur_stack_size);
            auto block_end      = lauf_asm_declare_block(b, cur_stack_size + 1);

            // Evaluate the condition and push it onto the stack.
            codegen_expr(ctx, b, expr->condition(), codegen_expr_mode::value);
            auto const_target = lauf_asm_inst_branch(b, block_if_true, block_if_false);

            if (const_target != block_if_false)
            {
                // Evaluate the if_true case.
                lauf_asm_build_block(b, block_if_true);
                codegen_expr(ctx, b, expr->if_true(), mode);
                lauf_asm_inst_jump(b, block_end);
            }

            if (const_target != block_if_true)
            {
                // Evaluate the if_false case.
                lauf_asm_build_block(b, block_if_false);
                codegen_expr(ctx, b, expr->if_false(), mode);
                lauf_asm_inst_jump(b, block_end);
            }

            // Continue, but in the new block.
            lauf_asm_build_block(b, block_end);
        });
}

template <typename ExprOrInit>
void constant_eval_impl(void* data, context& ctx, const clauf::type* type, const ExprOrInit* e)
{
    auto layout = codegen_lauf_layout(type);

    // We create a chunk that will hold the bytecode for our expression.
    auto chunk = ctx.consteval_chunk;
    {
        auto b = ctx.chunk_builder;
        lauf_asm_build_chunk(b, ctx.mod, chunk, {0, 0});

        if constexpr (std::is_same_v<ExprOrInit, clauf::expr>)
        {
            // Store the result of the expression in the native global.
            lauf_asm_inst_global_addr(b, ctx.consteval_result_global);
            codegen_expr(ctx, b, e, codegen_expr_mode::store);
        }
        else
        {
            lauf_asm_inst_global_addr(b, ctx.consteval_result_global);
            codegen_init(ctx, b, type, e);
        }

        lauf_asm_inst_return(b);
        lauf_asm_build_finish(b);
    }

    // We then execute that chunk.
    {
        auto program = lauf_asm_create_program_from_chunk(ctx.mod, chunk);
        lauf_asm_define_native_global(&program, ctx.consteval_result_global, data, layout.size);

        struct ph_data_t
        {
            const context&    ctx;
            const ExprOrInit* e;
        } ph_data = {ctx, e};
        auto ph   = [](void* data, lauf_runtime_process*, const char* msg) {
            auto [ctx, e] = *static_cast<ph_data_t*>(data);
            ctx.logger
                ->log(clauf::diagnostic_kind::error, "panic during constant evaluation '%s'", msg)
                .annotation(clauf::annotation_kind::primary, ctx.input->location_of(e),
                              "while evaluating expr here")
                .finish();
        };
        auto old_ph = lauf_vm_set_panic_handler(ctx.vm, {&ph_data, ph});

        auto success = lauf_vm_execute_oneshot(ctx.vm, program, nullptr, nullptr);
        if (!success)
            throw std::runtime_error("constant evaluation panic");

        lauf_vm_set_panic_handler(ctx.vm, old_ph);
    }
}

std::vector<unsigned char> constant_eval(context& ctx, const clauf::type* type,
                                         const clauf::init* init)
{
    auto                       layout = codegen_lauf_layout(type);
    std::vector<unsigned char> result;
    result.resize(layout.size);

    constant_eval_impl(result.data(), ctx, type, init);

    return result;
}

void codegen_global_init(context& ctx, lauf_asm_global* global, const clauf::variable_decl* decl)
{
    auto layout = codegen_lauf_layout(decl->type());

    if (decl->has_initializer())
    {
        auto init = constant_eval(ctx, decl->type(), decl->initializer());
        lauf_asm_define_data_global(ctx.mod, global, layout, init.data());
    }
    else
    {
        lauf_asm_define_data_global(ctx.mod, global, layout, nullptr);
    }
}

// Initializes the object whose address is on top of the stack.
void codegen_init(context& ctx, lauf_asm_builder* b, const clauf::type* type,
                  const clauf::init* init)
{
    if (auto lauf_type = codegen_lauf_type(type))
    {
        // Evaluate the initializer to a single stack value.
        CLAUF_ASSERT(clauf::is_scalar(type), "only scalars map to single stack values");

        dryad::visit_tree(
            init,
            [&](const clauf::empty_init*) {
                lauf_asm_inst_uint(b, 0);

                // Store it into the object.
                lauf_asm_inst_roll(b, 1);
                lauf_asm_inst_store_field(b, *lauf_type, 0);
            },
            [&](const clauf::braced_init*) {
                // No need to do anything, the children push the value.
            },
            [&](const clauf::expr_init* init) {
                codegen_expr(ctx, b, init->expression(), codegen_expr_mode::store);
            });
    }
    else if (auto array = dryad::node_try_cast<const clauf::array_type>(type))
    {
        auto elem_layout = codegen_lauf_layout(array->element_type());
        dryad::visit_node_all(
            init,
            [&](const clauf::empty_init*) {
                lauf_asm_inst_uint(b, 0);
                lauf_asm_inst_uint(b, array->size() * elem_layout.size);
                lauf_asm_inst_call_builtin(b, lauf_lib_memory_fill);
            },
            [&](const clauf::expr_init* init) {
                // We know that this is a string literal.
                auto str_literal = dryad::node_cast<clauf::string_literal_expr>(
                    dryad::node_cast<clauf::decay_expr>(init->expression())->child());
                auto str_length = std::strlen(str_literal->value()) + 1;
                auto str        = lauf_asm_build_string_literal(b, str_literal->value());

                // TODO: memset rest to zero.
                lauf_asm_inst_global_addr(b, str);
                if (str_length < array->size() * elem_layout.size)
                    lauf_asm_inst_uint(b, str_length);
                else
                    lauf_asm_inst_uint(b, array->size() * elem_layout.size);
                lauf_asm_inst_call_builtin(b, lauf_lib_memory_copy);
            },
            [&](const clauf::braced_init* init) {
                // If we are currently doing constant evaluation, or if we can't evaluate the
                // initializer at compile-time, we need to manually initialize each array element.
                if (b == ctx.chunk_builder || !clauf::is_constant_init(init))
                {
                    for (auto elem_init : init->initializers())
                    {
                        lauf_asm_inst_pick(b, 0);
                        codegen_init(ctx, b, array->element_type(), elem_init);

                        lauf_asm_inst_uint(b, elem_layout.size);
                        lauf_asm_inst_call_builtin(b, lauf_lib_memory_addr_add(
                                                          LAUF_LIB_MEMORY_ADDR_OVERFLOW_PANIC));
                    }

                    if (init->trailing_empty_inits() > 0)
                    {
                        lauf_asm_inst_uint(b, 0);
                        lauf_asm_inst_uint(b, init->trailing_empty_inits() * elem_layout.size);
                        lauf_asm_inst_call_builtin(b, lauf_lib_memory_fill);
                    }
                    else
                    {
                        lauf_asm_inst_pop(b, 0);
                    }
                }
                else
                {
                    // Otherwise, we can evaluate initializer, store it as global memory,
                    // and copy the values over.
                    auto bytes = constant_eval(ctx, type, init);

                    auto data = lauf_asm_build_data_literal(b, bytes.data(), bytes.size());
                    lauf_asm_inst_global_addr(b, data);
                    lauf_asm_inst_uint(b, array->size() * elem_layout.size);
                    lauf_asm_inst_call_builtin(b, lauf_lib_memory_copy);
                }
            });
    }
    else if (auto decl_type = dryad::node_try_cast<const clauf::decl_type>(type))
    {
        auto struct_       = dryad::node_cast<clauf::struct_decl>(decl_type->decl())->definition();
        auto struct_layout = codegen_lauf_layout(decl_type);

        dryad::visit_node_all(
            init,
            [&](const clauf::empty_init*) {
                lauf_asm_inst_uint(b, 0);
                lauf_asm_inst_uint(b, struct_layout.size);
                lauf_asm_inst_call_builtin(b, lauf_lib_memory_fill);
            },
            [&](const clauf::expr_init*) {
                CLAUF_UNREACHABLE("struct cannot be initialized by expression");
            },
            [&](const clauf::braced_init* init) {
                // If we are currently doing constant evaluation, or if we can't evaluate the
                // initializer at compile-time, we need to manually initialize each array element.
                if (b == ctx.chunk_builder || !clauf::is_constant_init(init))
                {
                    std::vector<lauf_asm_layout> member_layouts;
                    for (auto member : struct_->members())
                        member_layouts.push_back(codegen_lauf_layout(member->type()));

                    // At this point the top of the vstack is the address of the struct object.
                    auto member_index = 0u;
                    for (auto elem_init : init->initializers())
                    {
                        // We want to initialize the current member of the struct.
                        lauf_asm_inst_pick(b, 0);
                        lauf_asm_inst_aggregate_member(b, member_index, member_layouts.data(),
                                                       member_layouts.size());
                        codegen_init(ctx, b,
                                     (*std::next(struct_->members().begin(), member_index))->type(),
                                     elem_init);

                        member_index++;
                    }

                    for (auto i = 0u; i != init->trailing_empty_inits(); ++i)
                    {
                        // We want to memset the current member.
                        lauf_asm_inst_pick(b, 0);
                        lauf_asm_inst_aggregate_member(b, member_index, member_layouts.data(),
                                                       member_layouts.size());

                        lauf_asm_inst_uint(b, 0);
                        lauf_asm_inst_uint(b, member_layouts[member_index].size);
                        lauf_asm_inst_call_builtin(b, lauf_lib_memory_fill);
                    }

                    // Remove the base address of the struct.
                    lauf_asm_inst_pop(b, 0);
                }
                else
                {
                    // Otherwise, we can evaluate initializer, store it as global memory,
                    // and copy the values over.
                    auto bytes = constant_eval(ctx, type, init);

                    auto data = lauf_asm_build_data_literal(b, bytes.data(), bytes.size());
                    lauf_asm_inst_global_addr(b, data);
                    lauf_asm_inst_uint(b, struct_layout.size);
                    lauf_asm_inst_call_builtin(b, lauf_lib_memory_copy);
                }
            });
    }
    else
    {
        CLAUF_TODO("unimplemented initializer for non-scalar type");
    }
}

lauf_asm_function* codegen_function_body(context& ctx, const clauf::function_decl* decl)
{
    auto fn        = *ctx.functions->lookup(decl);
    ctx.local_vars = {};

    std::vector<const clauf::parameter_decl*> params;
    for (auto param : decl->parameters())
        params.push_back(param);

    auto b = ctx.body_builder;
    lauf_asm_build(b, ctx.mod, fn);

    // We create variables for all parameters and store the value into them.
    // Since parameters have been pushed onto the stack and are thus popped in reverse,
    // we need to iterate in reverse order.
    for (auto iter = params.rbegin(); iter != params.rend(); ++iter)
    {
        auto param_decl = *iter;

        // The corresponding local variable should be big enough to contain the entire object.
        auto layout = codegen_lauf_layout(param_decl->type());
        auto var    = lauf_asm_build_local(b, layout);
        ctx.local_vars.insert(param_decl, var);

        lauf_asm_inst_local_addr(b, var);

        if (auto type = codegen_lauf_type(param_decl->type()))
        {
            // If it's a first class, the argument on top of the vstack is the value directly.
            // We want to store that into our local variable.
            lauf_asm_inst_store_field(b, *type, 0);
        }
        else
        {
            // Otherwise, the argument on top of the vstack is a pointer to the struct
            // object. We want to copy that into the local variable.
            lauf_asm_inst_roll(b, 1);
            lauf_asm_inst_uint(b, layout.size);
            lauf_asm_inst_call_builtin(b, lauf_lib_memory_copy);
        }
    }

    // If we don't have a first class return type,
    // we get a pointer to write the result into.
    // Need to save that to access it on return.
    lauf_asm_local* return_ptr = nullptr;
    if (auto return_type = decl->type()->return_type();
        !clauf::is_void(return_type) && !is_first_class_type(return_type))
    {
        return_ptr = lauf_asm_build_local(b, lauf_asm_type_value.layout);
        lauf_asm_inst_local_addr(b, return_ptr);
        lauf_asm_inst_store_field(b, lauf_asm_type_value, 0);
    }

    lauf_asm_block* block_loop_end    = nullptr;
    lauf_asm_block* block_loop_header = nullptr;
    dryad::visit_tree(
        decl->body(),
        //=== statements ===//
        [&, anchor = lexy::input_location_anchor(ctx.input->buffer())] //
        (dryad::traverse_event_enter, const clauf::stmt* stmt) mutable {
            // Generate debug location for all instructions generated by a statement.
            auto location = ctx.input->location_of(stmt);
            auto expanded_location
                = lexy::get_input_location(ctx.input->buffer(), location.begin, anchor);

            lauf_asm_build_debug_location(b, {std::uint16_t(expanded_location.line_nr()),
                                              std::uint16_t(expanded_location.column_nr()), false});

            anchor = expanded_location.anchor();
        },
        [&](dryad::child_visitor<clauf::node_kind>, const clauf::expr_stmt* stmt) {
            // Evaluate and discard the expression.
            codegen_expr(ctx, b, stmt->expr(), codegen_expr_mode::discard);
        },
        [&](dryad::child_visitor<clauf::node_kind>, const clauf::return_stmt* stmt) {
            if (!stmt->has_expr())
            {
                // Do nothing to evaluate the expression, since there is none.
            }
            else if (return_ptr == nullptr)
            {
                // Return a first class type by evaluating the expression as a value.
                codegen_expr(ctx, b, stmt->expr(), codegen_expr_mode::value);
            }
            else
            {
                // Generate code for the return expression, storing it in the return ptr.
                // So first load the return ptr.
                lauf_asm_inst_local_addr(b, return_ptr);
                lauf_asm_inst_load_field(b, lauf_asm_type_value, 0);

                // Duplicate it, since that's the value we're returning.
                lauf_asm_inst_pick(b, 0);

                // Store it in the return pointer.
                codegen_expr(ctx, b, stmt->expr(), codegen_expr_mode::store);
            }

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

            // Evaluate the condition as a value.
            codegen_expr(ctx, b, stmt->condition(), codegen_expr_mode::value);
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

            // Evaluate condition in loop header as a value and branch.
            lauf_asm_build_block(b, block_loop_header);
            codegen_expr(ctx, b, stmt->condition(), codegen_expr_mode::value);
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
        [&](dryad::child_visitor<clauf::node_kind>, const clauf::variable_decl* decl) {
            if (decl->storage_duration() != clauf::storage_duration::static_)
            {
                auto layout = codegen_lauf_layout(decl->type());
                auto var    = lauf_asm_build_local(b, layout);
                ctx.local_vars.insert(decl, var);

                if (decl->has_initializer())
                {
                    lauf_asm_inst_local_addr(b, var);
                    codegen_init(ctx, b, decl->type(), decl->initializer());
                }
            }
        },
        //=== expression ===//
        [&](dryad::child_visitor<clauf::node_kind>, const clauf::expr*) {
            CLAUF_UNREACHABLE("need to manually visit expressions");
        });

    lauf_asm_build_debug_location(b, {0, 0, true});
    if (auto sig = lauf_asm_function_signature(fn); sig.output_count > 0)
        // Add an implicit return 0.
        lauf_asm_inst_uint(b, 0);
    lauf_asm_inst_return(b);

    lauf_asm_build_finish(b);
    return fn;
}

clauf::ffi_function* get_ffi_function(context& ctx, clauf::code& code,
                                      const clauf::function_decl* decl)
{
    std::vector<ffi_type*> types;
    for (auto param : decl->parameters())
        types.push_back(codegen_ffi_type(param->type()));

    ffi_cif cif;
    ffi_prep_cif(&cif, FFI_DEFAULT_ABI, unsigned(types.size()),
                 codegen_ffi_type(decl->type()->return_type()), types.data());

    // Find the native address of the function.
    auto fn_addr = dlsym(RTLD_DEFAULT, decl->name().c_str(*ctx.symbols));

    return code.add_ffi_function({cif, fn_addr, std::move(types)});
}

lauf_asm_function* codegen_native_trampoline(context& ctx, clauf::code& code,
                                             const clauf::function_decl* decl)
{
    auto                                      fn = *ctx.functions->lookup(decl);
    std::vector<const clauf::parameter_decl*> params;
    for (auto param : decl->parameters())
        params.push_back(param);

    auto b = ctx.body_builder;
    lauf_asm_build(b, ctx.mod, fn);

    // Create the argument array.
    auto arguments
        = lauf_asm_build_local(b, lauf_asm_array_layout(lauf_asm_type_value.layout, params.size()));

    // We create variables for all parameters and store the value into them.
    // Since parameters have been pushed onto the stack and are thus popped in reverse,
    // we need to iterate in reverse order.
    // We then store a pointer to the parameter in the arguments array.
    for (auto iter = params.rbegin(); iter != params.rend(); ++iter)
    {
        auto param_decl = *iter;
        auto type       = codegen_lauf_type(param_decl->type());

        if (auto ptr = dryad::node_try_cast<clauf::pointer_type>(param_decl->type());
            ptr != nullptr && ptr->native() == clauf::native_specifier::default_)
            lauf_asm_inst_call_builtin(b, translate_address_to_pointer);
        else if (ptr != nullptr && ptr->native() == clauf::native_specifier::string)
            lauf_asm_inst_call_builtin(b, translate_address_to_string);

        auto var = lauf_asm_build_local(b, type->layout);
        lauf_asm_inst_local_addr(b, var);
        lauf_asm_inst_store_field(b, *type, 0);

        lauf_asm_inst_local_addr(b, var);
        lauf_asm_inst_local_addr(b, arguments);
        lauf_asm_inst_uint(b, std::size_t(iter.base() - params.begin() - 1));
        lauf_asm_inst_array_element(b, lauf_asm_type_value.layout);
        lauf_asm_inst_store_field(b, lauf_asm_type_value, 0);
    }

    auto ffi_function = get_ffi_function(ctx, code, decl);
    if (ffi_function->addr == nullptr)
    {
        auto msg = lauf_asm_build_string_literal(b, "undefined reference to native function");
        lauf_asm_inst_global_addr(b, msg);
        lauf_asm_inst_panic(b);
    }

    if (clauf::is_void(decl->type()->return_type()))
    {
        lauf_asm_inst_null(b);
        lauf_asm_inst_local_addr(b, arguments);
        lauf_asm_inst_bytes(b, &ffi_function);
        lauf_asm_inst_call_builtin(b, call_native);
    }
    else
    {
        auto return_type  = codegen_lauf_type(decl->type()->return_type());
        auto return_value = lauf_asm_build_local(b, return_type->layout);

        lauf_asm_inst_local_addr(b, return_value);
        lauf_asm_inst_local_addr(b, arguments);
        lauf_asm_inst_bytes(b, &ffi_function);
        lauf_asm_inst_call_builtin(b, call_native);

        lauf_asm_inst_local_addr(b, return_value);
        lauf_asm_inst_load_field(b, *return_type, 0);
        if (auto ptr = dryad::node_try_cast<clauf::pointer_type>(decl->type()->return_type());
            ptr != nullptr && ptr->native() == clauf::native_specifier::default_)
            lauf_asm_inst_call_builtin(b, translate_pointer_to_address);
        else if (ptr != nullptr && ptr->native() == clauf::native_specifier::string)
            lauf_asm_inst_call_builtin(b, translate_string_to_address);
    }
    lauf_asm_inst_return(b);

    lauf_asm_build_finish(b);
    return fn;
}
} // namespace

//=== codegen ===//
clauf::codegen::codegen(lauf_vm* vm, diagnostic_logger& logger, const file& f,
                        const ast_symbol_interner& sym)
: _vm(vm), _logger(&logger), _file(&f), _symbols(&sym), _mod(lauf_asm_create_module("main module")),
  _body_builder(lauf_asm_create_builder(lauf_asm_default_build_options)),
  _chunk_builder(lauf_asm_create_builder(lauf_asm_default_build_options)),
  _consteval_chunk(lauf_asm_create_chunk(_mod)),
  _consteval_result_global(lauf_asm_add_global(_mod, LAUF_ASM_GLOBAL_READ_WRITE))
{
    lauf_asm_set_module_debug_path(_mod, f.path());
    lauf_asm_set_global_debug_name(_mod, _consteval_result_global,
                                   "constexpr_initialization_result");
}

void clauf::codegen::declare_global(const variable_decl* decl)
{
    if (!decl->is_definition())
        return;

    auto qualifiers = clauf::type_qualifiers_of(decl->type());
    auto is_const   = (qualifiers & clauf::qualified_type::const_) != 0;

    auto global = lauf_asm_add_global(_mod, is_const ? LAUF_ASM_GLOBAL_READ_ONLY
                                                     : LAUF_ASM_GLOBAL_READ_WRITE);
    lauf_asm_set_global_debug_name(_mod, global, decl->name().c_str(*_symbols));
    _globals.insert(decl, global);

    if (decl->is_constexpr())
    {
        // For an constexpr global, we need to set its value immediately, as it can be accessed
        // during integer constant evaluation.
        context ctx{_vm,
                    _logger,
                    _symbols,
                    _file,
                    _mod,
                    _consteval_chunk,
                    _consteval_result_global,
                    _body_builder,
                    _chunk_builder,
                    &_globals,
                    &_functions,
                    {}};
        codegen_global_init(ctx, global, decl);
    }
}

void clauf::codegen::declare_function(const function_decl* decl)
{
    if (!decl->is_definition() && decl->linkage() != clauf::linkage::native)
        return;

    auto parameter_count = std::distance(decl->parameters().begin(), decl->parameters().end());
    auto return_count    = [&] {
        auto return_type = decl->type()->return_type();
        if (clauf::is_void(return_type))
        {
            return 0;
        }
        else if (is_first_class_type(return_type))
        {
            return 1;
        }
        else
        {
            // Add one parameter for the return pointer.
            ++parameter_count;
            // We return the return pointer from the call.
            return 1;
        }
    }();

    auto name = decl->name().c_str(*_symbols);
    auto fn   = lauf_asm_add_function(_mod, name,
                                      {static_cast<std::uint8_t>(parameter_count),
                                       static_cast<std::uint8_t>(return_count)});
    _functions.insert(decl, fn);
    if (decl->linkage() == clauf::linkage::external)
        lauf_asm_export_function(fn);
}

std::size_t clauf::codegen::constant_eval_integer_expr(const expr* expr)
try
{
    if (auto integer = dryad::node_try_cast<clauf::integer_constant_expr>(expr))
        return std::size_t(integer->value());

    context ctx{_vm,
                _logger,
                _symbols,
                _file,
                _mod,
                _consteval_chunk,
                _consteval_result_global,
                _body_builder,
                _chunk_builder,
                &_globals,
                &_functions,
                {}};

    lauf_runtime_value result;
    constant_eval_impl(&result, ctx, expr->type(), expr);
    return std::size_t(result.as_uint);
}
catch (std::runtime_error&)
{
    return 0;
}

std::optional<clauf::code> clauf::codegen::finish(const ast& ast) &&
try
{
    context     ctx{_vm,
                _logger,
                _symbols,
                _file,
                _mod,
                _consteval_chunk,
                _consteval_result_global,
                _body_builder,
                _chunk_builder,
                &_globals,
                &_functions,
                    {}};
    clauf::code code(_mod);

    // Generate body for all lauf declarations.
    dryad::visit_tree(
        ast.tree,
        [&](const variable_decl* decl) {
            // We need to initialize all non-constexpr globals, because that hasn't happened before.
            if (decl->storage_duration() == storage_duration::static_ && decl->is_definition()
                && !decl->is_constexpr())
            {
                auto global = *ctx.globals->lookup(decl);
                codegen_global_init(ctx, global, decl);
            }
        },
        [&](const function_decl* decl) {
            if (decl->is_definition())
                codegen_function_body(ctx, decl);
            else if (decl->linkage() == clauf::linkage::native)
                codegen_native_trampoline(ctx, code, decl);
        });

    return code;
}
catch (std::runtime_error&)
{
    return std::nullopt;
}

