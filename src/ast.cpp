// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <clauf/ast.hpp>

#include <cstdio>

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
    case clauf::node_kind::expr_stmt:
        return "expression stmt";
    case clauf::node_kind::block_stmt:
        return "block stmt";
    case clauf::node_kind::function_type:
        return "function type";
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
            //=== decls ===//
            [&](const function_decl* d) { std::printf("'%s'", d->name().c_str(ast.symbols)); });

        std::putchar('\n');
        if (ev == dryad::traverse_event::enter)
            ++level;
    }
}

