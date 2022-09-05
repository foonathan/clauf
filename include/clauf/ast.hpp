// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#ifndef CLAUF_AST_HPP_INCLUDED
#define CLAUF_AST_HPP_INCLUDED

#include <dryad/abstract_node.hpp>
#include <dryad/node.hpp>
#include <dryad/node_map.hpp>
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

    //=== expressions ===//
    integer_constant_expr,
    identifier_expr,
    unary_expr,
    arithmetic_expr,
    comparison_expr,
    sequenced_expr,
    assignment_expr,
    conditional_expr,

    first_expr = integer_constant_expr,
    last_expr  = conditional_expr,

    //=== statements ===//
    decl_stmt,
    expr_stmt,
    builtin_stmt,
    block_stmt,

    first_stmt = decl_stmt,
    last_stmt  = block_stmt,

    //=== declarations ===//
    variable_decl,
    function_decl,

    first_decl = variable_decl,
    last_decl  = function_decl,
};

using node = dryad::node<node_kind>;

struct ast_symbol_id;
using ast_symbol = dryad::symbol<ast_symbol_id, std::uint32_t>;

class decl;
using decl_list = dryad::unlinked_node_list<decl>;

class stmt;
using stmt_list = dryad::unlinked_node_list<stmt>;
} // namespace clauf

//=== types ===//
namespace clauf
{
/// The base class of all C types in the AST.
struct type : dryad::abstract_node_range<node, node_kind::first_type, node_kind::last_type>
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
class function_type
: public dryad::basic_node<node_kind::function_type, dryad::container_node<type>>
{
public:
    explicit function_type(dryad::node_ctor ctor, type* return_type) : node_base(ctor)
    {
        insert_child_after(nullptr, return_type);
    }

    DRYAD_CHILD_NODE_GETTER(type, return_type, nullptr)
};
} // namespace clauf

//=== expr ===//
namespace clauf
{
/// Base class for all expressions.
class expr : public dryad::abstract_node_range<dryad::container_node<node>, node_kind::first_expr,
                                               node_kind::last_expr>
{
public:
    DRYAD_CHILD_NODE_GETTER(clauf::type, type, nullptr)

protected:
    explicit expr(dryad::node_ctor ctor, node_kind kind, clauf::type* type) : node_base(ctor, kind)
    {
        insert_child_after(nullptr, type);
    }
};

class integer_constant_expr : public dryad::basic_node<node_kind::integer_constant_expr, expr>
{
public:
    explicit integer_constant_expr(dryad::node_ctor ctor, clauf::type* ty, std::uint64_t value)
    : node_base(ctor, ty), _value(value)
    {}

    std::uint64_t value() const
    {
        return _value;
    }

private:
    std::uint64_t _value;
};

/// A name, which refers to a declaration, e.g. `int i`
class identifier_expr : public dryad::basic_node<node_kind::identifier_expr, expr>
{
public:
    explicit identifier_expr(dryad::node_ctor ctor, clauf::type* ty, clauf::decl* decl)
    : node_base(ctor, ty), _decl(decl)
    {}

    clauf::decl* declaration() const
    {
        return _decl;
    }

private:
    clauf::decl* _decl;
};

enum class unary_op : std::uint16_t
{
    plus,
    neg,
    bnot, // ~
    lnot, // !
};

/// A unary expression.
class unary_expr : public dryad::basic_node<node_kind::unary_expr, expr>
{
public:
    explicit unary_expr(dryad::node_ctor ctor, clauf::type* type, unary_op op, clauf::expr* child)
    : node_base(ctor, type)
    {
        set_op_impl(op);
        insert_child_after(this->type(), child);
    }

    unary_op op() const
    {
        return op_impl();
    }

    DRYAD_CHILD_NODE_GETTER(clauf::expr, child, type())

private:
    DRYAD_ATTRIBUTE_USER_DATA16(unary_op, op_impl);
};

template <node_kind Kind, typename OpT>
class binary_expr : public dryad::basic_node<Kind, expr>
{
public:
    explicit binary_expr(dryad::node_ctor ctor, clauf::type* type, OpT op, clauf::expr* left,
                         clauf::expr* right)
    : dryad::basic_node<Kind, expr>(ctor, type)
    {
        this->user_data16() = std::uint16_t(op);
        this->insert_children_after(this->type(), left, right);
    }

    OpT op() const
    {
        return OpT(this->user_data16());
    }

    DRYAD_CHILD_NODE_GETTER(clauf::expr, left, this->type())
    DRYAD_CHILD_NODE_GETTER(clauf::expr, right, this->left())

private:
    using dryad::basic_node<Kind, expr>::user_data16;
};

enum class arithmetic_op : std::uint16_t
{
    add,
    sub,
    mul,
    div,
    rem,

    band,
    bor,
    bxor,
    shl,
    shr,
};

/// Binary expression with signature T x T -> T.
using arithmetic_expr = binary_expr<node_kind::arithmetic_expr, arithmetic_op>;

enum class comparison_op
{
    eq,
    ne,
    lt,
    le,
    gt,
    ge,
};

/// Binary expression with signature T x T -> bool;
using comparison_expr = binary_expr<node_kind::comparison_expr, comparison_op>;

enum class sequenced_op
{
    land,
    lor,
    comma,
};

/// Binary expression whith special operator evaluation rules.
using sequenced_expr = binary_expr<node_kind::sequenced_expr, sequenced_op>;

enum class assignment_op : std::uint16_t
{
    none,
};

/// Assignment expression.
using assignment_expr = binary_expr<node_kind::assignment_expr, assignment_op>;

class conditional_expr : public dryad::basic_node<node_kind::conditional_expr, expr>
{
public:
    explicit conditional_expr(dryad::node_ctor ctor, clauf::type* type, clauf::expr* condition,
                              clauf::expr* if_true, clauf::expr* if_false)
    : node_base(ctor, type)
    {
        insert_children_after(this->type(), condition, if_true, if_false);
    }

    DRYAD_CHILD_NODE_GETTER(clauf::expr, condition, type())
    DRYAD_CHILD_NODE_GETTER(clauf::expr, if_true, condition())
    DRYAD_CHILD_NODE_GETTER(clauf::expr, if_false, if_true())
};
} // namespace clauf

//=== statements ===//
namespace clauf
{
/// Base class of all statements.
class stmt : public dryad::abstract_node_range<dryad::container_node<node>, node_kind::first_stmt,
                                               node_kind::last_stmt>
{
public:
    DRYAD_ABSTRACT_NODE_CTOR(stmt)
};

/// A statement that declares (multiple) things e.g. `int i, j;`
class decl_stmt : public dryad::basic_node<node_kind::decl_stmt, stmt>
{
public:
    explicit decl_stmt(dryad::node_ctor ctor, decl_list decls) : node_base(ctor)
    {
        insert_child_list_after(nullptr, decls);
    }

    auto declarations()
    {
        auto children = this->children();
        return dryad::make_node_range<decl>(children.begin(), children.end());
    }
    auto declarations() const
    {
        auto children = this->children();
        return dryad::make_node_range<decl>(children.begin(), children.end());
    }
};

/// A statement that evaluates an expression, e.g. `f();`
class expr_stmt : public dryad::basic_node<node_kind::expr_stmt, stmt>
{
public:
    explicit expr_stmt(dryad::node_ctor ctor, clauf::expr* expr) : node_base(ctor)
    {
        insert_child_after(nullptr, expr);
    }

    DRYAD_CHILD_NODE_GETTER(clauf::expr, expr, nullptr)
};

/// A statement that does a builtin action.
class builtin_stmt : public dryad::basic_node<node_kind::builtin_stmt, stmt>
{
public:
    enum builtin_t : std::uint16_t
    {
        print,
        assert,
    };

    explicit builtin_stmt(dryad::node_ctor ctor, builtin_t builtin, clauf::expr* expr)
    : node_base(ctor)
    {
        set_builtin_impl(builtin);
        insert_child_after(nullptr, expr);
    }

    builtin_t builtin() const
    {
        return builtin_impl();
    }

    DRYAD_CHILD_NODE_GETTER(clauf::expr, expr, nullptr)

private:
    DRYAD_ATTRIBUTE_USER_DATA16(builtin_t, builtin_impl);
};

/// A statement that contains a list of statements inside a block, e.g. { a; b; c}.
class block_stmt : public dryad::basic_node<node_kind::block_stmt, stmt>
{
public:
    DRYAD_NODE_CTOR(block_stmt)
    explicit block_stmt(dryad::node_ctor ctor, stmt_list stmts) : block_stmt(ctor)
    {
        this->insert_child_list_after(nullptr, stmts);
    }

    auto statements()
    {
        auto children = node_base::children();
        return dryad::make_node_range<stmt>(children.begin(), children.end());
    }
    auto statements() const
    {
        auto children = node_base::children();
        return dryad::make_node_range<stmt>(children.begin(), children.end());
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

    DRYAD_CHILD_NODE_GETTER(clauf::type, type, nullptr)

protected:
    explicit decl(dryad::node_ctor ctor, node_kind kind, ast_symbol name, clauf::type* type)
    : node_base(ctor, kind), _name(name)
    {
        insert_child_after(nullptr, type);
    }

private:
    ast_symbol _name;
};

/// A variable declaration.
class variable_decl : public dryad::basic_node<node_kind::variable_decl, decl>
{
public:
    explicit variable_decl(dryad::node_ctor ctor, ast_symbol name, clauf::type* type)
    : node_base(ctor, name, type)
    {}
};

/// A function declaration.
class function_decl : public dryad::basic_node<node_kind::function_decl, decl>
{
public:
    explicit function_decl(dryad::node_ctor ctor, ast_symbol name, clauf::type* type,
                           clauf::block_stmt* block)
    : node_base(ctor, name, type)
    {
        insert_child_after(this->type(), block);
    }

    DRYAD_CHILD_NODE_GETTER(clauf::block_stmt, body, type())
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
    explicit translation_unit(dryad::node_ctor ctor, decl_list decls) : node_base(ctor)
    {
        insert_child_list_after(nullptr, decls);
    }

    auto declarations()
    {
        auto children = node_base::children();
        return dryad::make_node_range<decl>(children.begin(), children.end());
    }
    auto declarations() const
    {
        auto children = node_base::children();
        return dryad::make_node_range<decl>(children.begin(), children.end());
    }
};

/// The location of an AST node in the input.
struct location
{
    const char* begin;
    const char* end;

    location() : begin(nullptr), end(nullptr) {}
    location(const char* pos) : begin(pos), end(pos) {}
    location(const char* begin, const char* end) : begin(begin), end(end) {}

    bool is_synthesized() const
    {
        return begin != nullptr && end != nullptr;
    }
};

/// The entire AST of a source file.
struct ast
{
    dryad::symbol_interner<ast_symbol_id, char, std::uint32_t> symbols;
    dryad::tree<node_kind>                                     tree;
    dryad::node_map<node, location>                            locations;

    translation_unit* root()
    {
        return dryad::node_cast<translation_unit>(tree.root());
    }
    const translation_unit* root() const
    {
        return dryad::node_cast<translation_unit>(tree.root());
    }

    template <typename T, typename... Args>
    T* create(location loc, Args&&... args)
    {
        auto node = tree.template create<T>(DRYAD_FWD(args)...);
        locations.insert(node, loc);
        return node;
    }

    location location_of(const node* n) const
    {
        return *locations.lookup(n);
    }
};

void dump_ast(const ast& ast);
} // namespace clauf

#endif // CLAUF_AST_HPP_INCLUDED

