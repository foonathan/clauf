// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <clauf/ast.hpp>

#include <cstdio>

void clauf::dump_ast(const ast& ast)
{
    auto level        = 0;
    auto print_indent = [&] {
        for (auto i = 0; i < level; ++i)
            std::putchar(' ');
        std::printf("- ");
    };
    auto print_end = [&] { std::putchar('\n'); };

    dryad::visit_all(
        ast.tree,
        [&](const translation_unit*) {
            // We do not print anything here.
        },
        //=== types ===//
        [&](const builtin_type* builtin) {
            print_indent();
            switch (builtin->type_kind())
            {
            case builtin_type::int_:
                std::printf("int");
                break;
            }
            print_end();
        },
        [&](dryad::traverse_event ev, const function_type*) {
            if (ev == dryad::traverse_event::enter)
            {
                print_indent();
                std::printf("function type");
                print_end();
                ++level;
            }
            else
            {
                --level;
            }
        },
        //=== decls ===//
        [&](dryad::traverse_event ev, const function_decl* d) {
            if (ev == dryad::traverse_event::enter)
            {
                print_indent();
                std::printf("function: %s", d->name().c_str(ast.symbols));
                print_end();
                ++level;
            }
            else
            {
                --level;
            }
        });
}

