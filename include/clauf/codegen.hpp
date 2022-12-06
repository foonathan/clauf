// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#ifndef CLAUF_CODEGEN_HPP_INCLUDED
#define CLAUF_CODEGEN_HPP_INCLUDED

#include <clauf/ast.hpp>
#include <lauf/asm/builder.h>
#include <lauf/asm/module.h>
#include <lauf/vm.h>
#include <vector>

namespace clauf
{
class diagnostic_logger;

class codegen
{
public:
    explicit codegen(lauf_vm* vm, diagnostic_logger& logger, const file& f,
                     const ast_symbol_interner& sym);

    codegen(const codegen&)            = delete;
    codegen& operator=(const codegen&) = delete;

    ~codegen()
    {
        lauf_asm_destroy_builder(_builder);
    }

    void declare_global(const variable_decl* decl);
    void declare_function(const function_decl* decl);

    std::size_t constant_eval_integer_expr(const expr* expr);

    lauf_asm_module* finish(const ast& ast) &&;

private:
    lauf_vm*                   _vm;
    diagnostic_logger*         _logger;
    const file*                _file;
    const ast_symbol_interner* _symbols;

    lauf_asm_module*  _mod;
    lauf_asm_builder* _builder;
    lauf_asm_chunk*   _consteval_chunk;
    lauf_asm_global*  _consteval_result_global;

    dryad::node_map<const clauf::variable_decl, lauf_asm_global*>   _globals;
    dryad::node_map<const clauf::function_decl, lauf_asm_function*> _functions;
};
} // namespace clauf

#endif // CLAUF_CODEGEN_HPP_INCLUDED

