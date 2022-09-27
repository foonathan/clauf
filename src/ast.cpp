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
        [&](const clauf::function_type* ty) -> clauf::type* {
            clauf::type_list params;
            for (auto param : ty->parameters())
                params.push_back(clone(creator, param));

            return creator.create<clauf::function_type>(clone(creator, ty->return_type()), params);
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
    case clauf::node_kind::integer_constant_expr:
        return "integer constant expr";
    case clauf::node_kind::identifier_expr:
        return "identifier expr";
    case clauf::node_kind::function_call_expr:
        return "function call expr";
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
            case clauf::builtin_type::int_:
                std::printf("int");
                break;
            }
        },
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

