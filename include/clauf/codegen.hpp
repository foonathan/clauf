// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#ifndef CLAUF_CODEGEN_HPP_INCLUDED
#define CLAUF_CODEGEN_HPP_INCLUDED

#include <clauf/ast.hpp>
#include <deque>
#include <ffi.h>
#include <lauf/asm/builder.h>
#include <lauf/asm/module.h>
#include <lauf/vm.h>
#include <optional>
#include <vector>

namespace clauf
{
class diagnostic_logger;

struct ffi_function
{
    ffi_cif                cif;
    void*                  addr;
    std::vector<ffi_type*> argument_types;
};

class code
{
public:
    explicit code(lauf_asm_module* mod) : _module(mod) {}

    ~code()
    {
        if (_module != nullptr)
            lauf_asm_destroy_module(_module);
    }

    code(code&& other) noexcept : _module(other._module), _functions(std::move(other._functions))
    {
        other._module = nullptr;
    }
    code& operator=(code&& other) noexcept
    {
        std::swap(_module, other._module);
        std::swap(_functions, other._functions);
        return *this;
    }

    lauf_asm_module* module() const
    {
        return _module;
    }

    ffi_function* add_ffi_function(ffi_function fn)
    {
        _functions.push_back(std::move(fn));
        return &_functions.back();
    }

private:
    lauf_asm_module*         _module;
    std::deque<ffi_function> _functions;
};

class codegen
{
public:
    explicit codegen(lauf_vm* vm, diagnostic_logger& logger, const file& f,
                     const ast_symbol_interner& sym);

    codegen(const codegen&)            = delete;
    codegen& operator=(const codegen&) = delete;

    ~codegen()
    {
        lauf_asm_destroy_builder(_body_builder);
        lauf_asm_destroy_builder(_chunk_builder);
    }

    void declare_global(const variable_decl* decl);
    void declare_function(const function_decl* decl);

    std::size_t constant_eval_integer_expr(const expr* expr);

    std::optional<code> finish(const ast& ast) &&;

private:
    lauf_vm*                   _vm;
    diagnostic_logger*         _logger;
    const file*                _file;
    const ast_symbol_interner* _symbols;

    lauf_asm_module*  _mod;
    lauf_asm_builder* _body_builder;
    lauf_asm_builder* _chunk_builder;
    lauf_asm_chunk*   _consteval_chunk;
    lauf_asm_global*  _consteval_result_global;

    dryad::node_map<const clauf::variable_decl, lauf_asm_global*>   _globals;
    dryad::node_map<const clauf::function_decl, lauf_asm_function*> _functions;
};
} // namespace clauf

#endif // CLAUF_CODEGEN_HPP_INCLUDED

