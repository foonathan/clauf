// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#ifndef CLAUF_AST_HPP_INCLUDED
#define CLAUF_AST_HPP_INCLUDED

#include <dryad/abstract_node.hpp>
#include <dryad/node.hpp>
#include <dryad/symbol.hpp>
#include <dryad/tree.hpp>

namespace clauf
{
enum class node_kind
{
    translation_unit,

    //=== types ===//
    builtin_type,
    function_type,

    first_type = builtin_type,
    last_type  = function_type,

    //=== declarations ===//
    function_decl,

    first_decl = function_decl,
    last_decl  = function_decl,
};

using node = dryad::node<node_kind>;

struct ast_symbol_id;
using ast_symbol = dryad::symbol<ast_symbol_id, std::uint32_t>;
} // namespace clauf

//=== types ===//
namespace clauf
{
/// The baseclass of all C types in the AST.
struct type : dryad::abstract_node_range<dryad::container_node<node>, node_kind::first_type,
                                         node_kind::last_type>
{
    DRYAD_ABSTRACT_NODE_CTOR(type)
};

/// A builtin type like int.
class builtin_type : public dryad::basic_node<node_kind::builtin_type, type>
{
public:
    enum type_kind_t : std::uint16_t
    {
        int_,
    };

    explicit builtin_type(dryad::node_ctor ctor, type_kind_t kind) : node_base(ctor)
    {
        set_type_kind_impl(kind);
    }

    type_kind_t type_kind() const
    {
        return type_kind_impl();
    }

private:
    DRYAD_ATTRIBUTE_USER_DATA16(type_kind_t, type_kind_impl);
};

/// A function type like int(void).
class function_type : public dryad::basic_node<node_kind::function_type, type>
{
public:
    explicit function_type(dryad::node_ctor ctor, type* return_type) : node_base(ctor)
    {
        insert_child_after(nullptr, return_type);
    }

    type* return_type()
    {
        auto first_child = children().front();
        return dryad::node_cast<type>(first_child);
    }
};
} // namespace clauf

//=== declaration ===//
namespace clauf
{
/// The baseclass of all declarations in the AST.
class decl : public dryad::abstract_node_range<dryad::container_node<node>, node_kind::first_decl,
                                               node_kind::last_decl>
{
public:
    ast_symbol name() const
    {
        return _name;
    }
    void set_name(ast_symbol name)
    {
        _name = name;
    }

    const type* type() const
    {
        auto first_child = children().front();
        return dryad::node_cast<clauf::type>(first_child);
    }

protected:
    explicit decl(dryad::node_ctor ctor, node_kind kind, ast_symbol name, clauf::type* type)
    : node_base(ctor, kind), _name(name)
    {
        insert_child_after(nullptr, type);
    }

private:
    ast_symbol _name;
};

/// A function declaration.
class function_decl : public dryad::basic_node<node_kind::function_decl, decl>
{
public:
    explicit function_decl(dryad::node_ctor ctor, ast_symbol name, clauf::type* type)
    : node_base(ctor, name, type)
    {}
};
} // namespace clauf

//=== translation_unit ===//
namespace clauf
{
/// A C source file.
class translation_unit
: public dryad::basic_node<node_kind::translation_unit, dryad::container_node<node>>
{
public:
    DRYAD_NODE_CTOR(translation_unit)

    void add_declaration(decl* d)
    {
        insert_child_after(nullptr, d);
    }
};

struct ast
{
    dryad::symbol_interner<ast_symbol_id, char, std::uint32_t> symbols;
    dryad::tree<node_kind>                                     tree;

    template <typename T, typename... Args>
    T* create(Args&&... args)
    {
        return tree.template create<T>(DRYAD_FWD(args)...);
    }
};

void dump_ast(const ast& ast);
} // namespace clauf

#endif // CLAUF_AST_HPP_INCLUDED

