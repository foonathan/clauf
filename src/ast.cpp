// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <clauf/ast.hpp>

#include <cstdio>

clauf::type* clauf::clone(type_forest::node_creator creator, const type* ty)
{
    return dryad::visit_node_all(
        ty,
        [&](const clauf::builtin_type* ty) -> clauf::type* {
            return creator.create<clauf::builtin_type>(ty->type_kind());
        },
        [&](const clauf::pointer_type* ty) -> clauf::type* {
            return creator.create<clauf::pointer_type>(clone(creator, ty->pointee_type()));
        },
        [&](const clauf::function_type* ty) -> clauf::type* {
            clauf::type_list params;
            for (auto param : ty->parameters())
                params.push_back(clone(creator, param));

            return creator.create<clauf::function_type>(clone(creator, ty->return_type()), params);
        });
}

clauf::type* clauf::make_unsigned(type_forest::node_creator creator, const type* ty)
{
    if (!dryad::node_has_kind<clauf::builtin_type>(ty))
        return nullptr;

    auto kind = dryad::node_cast<clauf::builtin_type>(ty)->type_kind();
    switch (kind)
    {
    case clauf::builtin_type::uint8:
    case clauf::builtin_type::uint16:
    case clauf::builtin_type::uint32:
    case clauf::builtin_type::uint64:
        return creator.create<clauf::builtin_type>(kind);

    case clauf::builtin_type::sint8:
        return creator.create<clauf::builtin_type>(clauf::builtin_type::uint8);
    case clauf::builtin_type::sint16:
        return creator.create<clauf::builtin_type>(clauf::builtin_type::uint16);
    case clauf::builtin_type::sint32:
        return creator.create<clauf::builtin_type>(clauf::builtin_type::uint32);
    case clauf::builtin_type::sint64:
        return creator.create<clauf::builtin_type>(clauf::builtin_type::uint64);

    case clauf::builtin_type::void_:
    case clauf::builtin_type::nullptr_t:
        return nullptr;
    }
}

bool clauf::is_same(const type* lhs, const type* rhs)
{
    if (lhs == rhs)
        return true;

    return type_hasher::is_equal_base(lhs, rhs);
}

bool clauf::is_void(const type* ty)
{
    if (auto builtin = dryad::node_try_cast<clauf::builtin_type>(ty))
        return builtin->type_kind() == clauf::builtin_type::void_;
    else
        return false;
}

bool clauf::is_signed_int(const type* ty)
{
    auto builtin = dryad::node_try_cast<clauf::builtin_type>(ty);
    if (builtin == nullptr)
        return false;

    switch (builtin->type_kind())
    {
    case builtin_type::sint8:
    case builtin_type::sint16:
    case builtin_type::sint32:
    case builtin_type::sint64:
        return true;

    case builtin_type::void_:
    case builtin_type::nullptr_t:
    case builtin_type::uint8:
    case builtin_type::uint16:
    case builtin_type::uint32:
    case builtin_type::uint64:
        return false;
    }
}
bool clauf::is_unsigned_int(const type* ty)
{
    auto builtin = dryad::node_try_cast<clauf::builtin_type>(ty);
    if (builtin == nullptr)
        return false;

    switch (builtin->type_kind())
    {
    case builtin_type::uint8:
    case builtin_type::uint16:
    case builtin_type::uint32:
    case builtin_type::uint64:
        return true;

    case builtin_type::void_:
    case builtin_type::nullptr_t:
    case builtin_type::sint8:
    case builtin_type::sint16:
    case builtin_type::sint32:
    case builtin_type::sint64:
        return false;
    }
}
bool clauf::is_integer(const type* ty)
{
    return is_signed_int(ty) || is_unsigned_int(ty);
}

bool clauf::is_arithmetic(const type* ty)
{
    return is_integer(ty);
}

bool clauf::is_pointer(const type* ty)
{
    return dryad::node_has_kind<clauf::pointer_type>(ty);
}

bool clauf::is_scalar(const type* ty)
{
    return clauf::is_arithmetic(ty) || clauf::is_pointer(ty);
}

bool clauf::is_complete_object_type(const type* ty)
{
    if (dryad::node_has_kind<clauf::function_type>(ty))
        return false;

    return !clauf::is_void(ty);
}

unsigned clauf::integer_rank_of(const type* ty)
{
    if (!dryad::node_has_kind<clauf::builtin_type>(ty))
        return unsigned(-1);

    auto kind = dryad::node_cast<clauf::builtin_type>(ty)->type_kind();
    switch (kind)
    {
    case clauf::builtin_type::sint8:
    case clauf::builtin_type::uint8:
        return 8;

    case clauf::builtin_type::sint16:
    case clauf::builtin_type::uint16:
        return 16;

    case clauf::builtin_type::sint32:
    case clauf::builtin_type::uint32:
        return 32;

    case clauf::builtin_type::sint64:
    case clauf::builtin_type::uint64:
        return 64;

    case clauf::builtin_type::void_:
    case clauf::builtin_type::nullptr_t:
        return unsigned(-1);
    }
}

bool clauf::is_lvalue(const expr* e)
{
    if (dryad::node_has_kind<clauf::identifier_expr>(e))
        return true;
    else if (auto unary = dryad::node_try_cast<clauf::unary_expr>(e))
        return unary->op() == clauf::unary_op::deref;
    else
        return false;
}

bool clauf::is_modifiable_lvalue(const expr* e)
{
    return is_lvalue(e) && is_complete_object_type(e->type());
}

bool clauf::is_nullptr_constant(const expr* e)
{
    if (auto integer_constant = dryad::node_try_cast<integer_constant_expr>(e))
    {
        return integer_constant->value() == 0;
    }
    else if (auto cast = dryad::node_try_cast<cast_expr>(e))
    {
        if (!clauf::is_void(cast->type()))
            return false;

        return is_nullptr_constant(cast->child());
    }
    else
    {
        return dryad::node_has_kind<nullptr_constant_expr>(e);
    }
}

clauf::name clauf::get_name(const declarator* decl)
{
    return dryad::visit_node_all(
        decl, [](const name_declarator* decl) { return decl->name(); },
        [](const function_declarator* decl) { return get_name(decl->child()); },
        [](const pointer_declarator* decl) { return get_name(decl->child()); },
        [](const init_declarator* decl) { return get_name(decl->child()); });
}

clauf::expr* clauf::get_init(const declarator* decl)
{
    if (auto init = dryad::node_try_cast<clauf::init_declarator>(decl))
        return init->initializer();
    else
        return nullptr;
}

const clauf::type* clauf::get_type(type_forest& types, const declarator* decl,
                                   const type* decl_type)
{
    return dryad::visit_node_all(
        decl, //
        [&](const clauf::name_declarator*) { return decl_type; },
        [&](const clauf::pointer_declarator* decl) {
            auto child_type = get_type(types, decl->child(), decl_type);
            return types.build([&](clauf::type_forest::node_creator creator) {
                return creator.create<clauf::pointer_type>(clauf::clone(creator, child_type));
            });
        },
        [&](const clauf::function_declarator* decl) {
            return types.build([&](clauf::type_forest::node_creator creator) {
                clauf::type_list parameter_types;
                for (auto param : decl->parameters())
                    parameter_types.push_back(clauf::clone(creator, param->type()));

                auto return_type = clauf::clone(creator, get_type(types, decl->child(), decl_type));
                return creator.create<clauf::function_type>(return_type, parameter_types);
            });
        },
        [&](const clauf::init_declarator* decl) {
            return get_type(types, decl->child(), decl_type);
        });
}

namespace
{
const char* to_string(clauf::node_kind kind)
{
    switch (kind)
    {
    case clauf::node_kind::translation_unit:
        return "translation unit";
    case clauf::node_kind::nullptr_constant_expr:
        return "nullptr constant expr";
    case clauf::node_kind::integer_constant_expr:
        return "integer constant expr";
    case clauf::node_kind::identifier_expr:
        return "identifier expr";
    case clauf::node_kind::function_call_expr:
        return "function call expr";
    case clauf::node_kind::cast_expr:
        return "cast expr";
    case clauf::node_kind::unary_expr:
        return "unary expr";
    case clauf::node_kind::arithmetic_expr:
        return "arithmetic expr";
    case clauf::node_kind::comparison_expr:
        return "comparison expr";
    case clauf::node_kind::sequenced_expr:
        return "sequenced expr";
    case clauf::node_kind::assignment_expr:
        return "assignment expr";
    case clauf::node_kind::conditional_expr:
        return "conditional expr";
    case clauf::node_kind::decl_stmt:
        return "decl stmt";
    case clauf::node_kind::expr_stmt:
        return "expr stmt";
    case clauf::node_kind::builtin_stmt:
        return "builtin stmt";
    case clauf::node_kind::return_stmt:
        return "return stmt";
    case clauf::node_kind::break_stmt:
        return "break stmt";
    case clauf::node_kind::continue_stmt:
        return "continue stmt";
    case clauf::node_kind::if_stmt:
        return "if stmt";
    case clauf::node_kind::while_stmt:
        return "while stmt";
    case clauf::node_kind::block_stmt:
        return "block stmt";
    case clauf::node_kind::variable_decl:
        return "variable decl";
    case clauf::node_kind::parameter_decl:
        return "parameter decl";
    case clauf::node_kind::function_decl:
        return "function decl";
    }
}

void dump_type(const clauf::type* ty)
{
    dryad::visit_tree(
        ty,
        [](const clauf::builtin_type* ty) {
            switch (ty->type_kind())
            {
            case clauf::builtin_type::void_:
                std::printf("void");
                break;
            case clauf::builtin_type::nullptr_t:
                std::printf("nullptr_t");
                break;
            case clauf::builtin_type::sint8:
                std::printf("sint8");
                break;
            case clauf::builtin_type::uint8:
                std::printf("uint8");
                break;
            case clauf::builtin_type::sint16:
                std::printf("sint16");
                break;
            case clauf::builtin_type::uint16:
                std::printf("uint16");
                break;
            case clauf::builtin_type::sint32:
                std::printf("sint32");
                break;
            case clauf::builtin_type::uint32:
                std::printf("uint32");
                break;
            case clauf::builtin_type::sint64:
                std::printf("sint64");
                break;
            case clauf::builtin_type::uint64:
                std::printf("uint64");
                break;
            }
        },
        [](dryad::traverse_event_enter, const clauf::pointer_type*) { std::printf("* "); },
        [](dryad::child_visitor<clauf::type_node_kind> visitor, const clauf::function_type* ty) {
            std::printf("(");
            for (auto param : ty->parameters())
                visitor(param);
            std::printf(") -> ");
            visitor(ty->return_type());
        });
}
} // namespace

void clauf::dump_ast(const ast& ast)
{
    auto level = 0;
    for (auto [ev, node] : dryad::traverse(ast.tree))
    {
        if (ev == dryad::traverse_event::exit)
        {
            --level;
            continue;
        }

        for (auto i = 0; i < level; ++i)
            std::printf("  ");
        std::printf("- %s: ", to_string(node->kind()));

        dryad::visit_node(
            node,
            //=== expr ===//
            [&](const integer_constant_expr* expr) {
                std::printf("%ld : ", expr->value());
                dump_type(expr->type());
            },
            [&](const identifier_expr* expr) {
                std::printf("'%s' : ", expr->declaration()->name().c_str(ast.symbols));
                dump_type(expr->type());
            },
            [&](const cast_expr* expr) { dump_type(expr->type()); },
            [&](const unary_expr* expr) {
                switch (expr->op())
                {
                case unary_op::plus:
                    std::printf("+");
                    break;
                case unary_op::neg:
                    std::printf("-");
                    break;
                case unary_op::bnot:
                    std::printf("~");
                    break;
                case unary_op::lnot:
                    std::printf("!");
                    break;

                case unary_op::pre_inc:
                    std::printf("++ (pre)");
                    break;
                case unary_op::pre_dec:
                    std::printf("-- (pre)");
                    break;
                case unary_op::post_inc:
                    std::printf("++ (post)");
                    break;
                case unary_op::post_dec:
                    std::printf("-- (post)");
                    break;

                case unary_op::address:
                    std::printf("&");
                case unary_op::deref:
                    std::printf("*");
                }
                std::printf(" : ");
                dump_type(expr->type());
            },
            [&](const arithmetic_expr* expr) {
                switch (expr->op())
                {
                case arithmetic_op::add:
                    std::printf("+");
                    break;
                case arithmetic_op::sub:
                    std::printf("-");
                    break;
                case arithmetic_op::mul:
                    std::printf("*");
                    break;
                case arithmetic_op::div:
                    std::printf("/");
                    break;
                case arithmetic_op::rem:
                    std::printf("%%");
                    break;
                case arithmetic_op::band:
                    std::printf("&");
                    break;
                case arithmetic_op::bor:
                    std::printf("|");
                    break;
                case arithmetic_op::bxor:
                    std::printf("^");
                    break;
                case arithmetic_op::shl:
                    std::printf("<<");
                    break;
                case arithmetic_op::shr:
                    std::printf(">>");
                    break;
                }
                std::printf(" : ");
                dump_type(expr->type());
            },
            [&](const comparison_expr* expr) {
                switch (expr->op())
                {
                case comparison_op::eq:
                    std::printf("==");
                    break;
                case comparison_op::ne:
                    std::printf("!=");
                    break;
                case comparison_op::lt:
                    std::printf("<");
                    break;
                case comparison_op::le:
                    std::printf("<=");
                    break;
                case comparison_op::gt:
                    std::printf(">");
                    break;
                case comparison_op::ge:
                    std::printf(">=");
                    break;
                }
                std::printf(" : ");
                dump_type(expr->type());
            },
            [&](const sequenced_expr* expr) {
                switch (expr->op())
                {
                case sequenced_op::land:
                    std::printf("&&");
                    break;
                case sequenced_op::lor:
                    std::printf("||");
                    break;
                case sequenced_op::comma:
                    std::printf(",");
                    break;
                }
                std::printf(" : ");
                dump_type(expr->type());
            },
            [&](const assignment_expr* expr) {
                switch (expr->op())
                {
                case assignment_op::none:
                    std::printf("=");
                    break;

                case assignment_op::add:
                    std::printf("+=");
                    break;
                case assignment_op::sub:
                    std::printf("-=");
                    break;
                case assignment_op::mul:
                    std::printf("*=");
                    break;
                case assignment_op::div:
                    std::printf("/=");
                    break;
                case assignment_op::rem:
                    std::printf("%%=");
                    break;
                case assignment_op::band:
                    std::printf("&=");
                    break;
                case assignment_op::bor:
                    std::printf("|=");
                    break;
                case assignment_op::bxor:
                    std::printf("^=");
                    break;
                case assignment_op::shl:
                    std::printf("<<=");
                    break;
                case assignment_op::shr:
                    std::printf(">>=");
                    break;
                }
                std::printf(" : ");
                dump_type(expr->type());
            },
            //=== stmt ===//
            [&](const builtin_stmt* stmt) {
                switch (stmt->builtin())
                {
                case builtin_stmt::print:
                    std::printf("__clauf_print");
                    break;
                case builtin_stmt::assert:
                    std::printf("__clauf_assert");
                    break;
                }
            },
            [&](const while_stmt* stmt) {
                switch (stmt->loop_kind())
                {
                case while_stmt::loop_while:
                    std::printf("while ...");
                    break;
                case while_stmt::loop_do_while:
                    std::printf("do ... while");
                    break;
                }
            },
            //=== decls ===//
            [&](const decl* d) {
                std::printf("'%s' : ", d->name().c_str(ast.symbols));
                dump_type(d->type());
            });

        std::putchar('\n');
        if (ev == dryad::traverse_event::enter)
            ++level;
    }
}

