// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <clauf/ast.hpp>

#include <cstdio>

void clauf::decl_stmt::add_declaration(decl* d)
{
    insert_child_after(nullptr, d);
}

namespace
{
const char* to_string(clauf::node_kind kind)
{
    switch (kind)
    {
    case clauf::node_kind::translation_unit:
        return "translation unit";
    case clauf::node_kind::builtin_type:
        return "builtin type";
    case clauf::node_kind::integer_constant_expr:
        return "integer constant expr";
    case clauf::node_kind::unary_expr:
        return "unary expr";
    case clauf::node_kind::binary_expr:
        return "binary expr";
    case clauf::node_kind::sequenced_binary_expr:
        return "sequenced binary expr";
    case clauf::node_kind::conditional_expr:
        return "conditional expr";
    case clauf::node_kind::decl_stmt:
        return "decl stmt";
    case clauf::node_kind::expr_stmt:
        return "expr stmt";
    case clauf::node_kind::builtin_stmt:
        return "builtin stmt";
    case clauf::node_kind::block_stmt:
        return "block stmt";
    case clauf::node_kind::function_type:
        return "function type";
    case clauf::node_kind::variable_decl:
        return "variable decl";
    case clauf::node_kind::function_decl:
        return "function decl";
    }
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
            //=== types ===//
            [&](const builtin_type* builtin) {
                switch (builtin->type_kind())
                {
                case builtin_type::int_:
                    std::printf("int");
                    break;
                }
            },
            //=== expr ===//
            [&](const integer_constant_expr* expr) { std::printf("%ld", expr->value()); },
            [&](const unary_expr* expr) {
                switch (expr->op())
                {
                case unary_expr::plus:
                    std::printf("+");
                    break;
                case unary_expr::neg:
                    std::printf("-");
                    break;
                case unary_expr::bnot:
                    std::printf("~");
                    break;
                case unary_expr::lnot:
                    std::printf("!");
                    break;
                }
            },
            [&](const binary_expr* expr) {
                switch (expr->op())
                {
                case binary_expr::add:
                    std::printf("+");
                    break;
                case binary_expr::sub:
                    std::printf("-");
                    break;
                case binary_expr::mul:
                    std::printf("*");
                    break;
                case binary_expr::div:
                    std::printf("/");
                    break;
                case binary_expr::rem:
                    std::printf("%%");
                    break;
                case binary_expr::band:
                    std::printf("&");
                    break;
                case binary_expr::bor:
                    std::printf("|");
                    break;
                case binary_expr::bxor:
                    std::printf("^");
                    break;
                case binary_expr::shl:
                    std::printf("<<");
                    break;
                case binary_expr::shr:
                    std::printf(">>");
                    break;
                case binary_expr::eq:
                    std::printf("==");
                    break;
                case binary_expr::ne:
                    std::printf("!=");
                    break;
                case binary_expr::lt:
                    std::printf("<");
                    break;
                case binary_expr::le:
                    std::printf("<=");
                    break;
                case binary_expr::gt:
                    std::printf(">");
                    break;
                case binary_expr::ge:
                    std::printf(">=");
                    break;
                }
            },
            [&](const sequenced_binary_expr* expr) {
                switch (expr->op())
                {
                case sequenced_binary_expr::land:
                    std::printf("&&");
                    break;
                case sequenced_binary_expr::lor:
                    std::printf("||");
                    break;
                case sequenced_binary_expr::comma:
                    std::printf(",");
                    break;
                }
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
            //=== decls ===//
            [&](const decl* d) { std::printf("'%s'", d->name().c_str(ast.symbols)); });

        std::putchar('\n');
        if (ev == dryad::traverse_event::enter)
            ++level;
    }
}

