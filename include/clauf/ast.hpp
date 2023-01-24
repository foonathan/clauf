// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#ifndef CLAUF_AST_HPP_INCLUDED
#define CLAUF_AST_HPP_INCLUDED

#include <dryad/abstract_node.hpp>
#include <dryad/hash_forest.hpp>
#include <dryad/node.hpp>
#include <dryad/node_map.hpp>
#include <dryad/symbol.hpp>
#include <dryad/tree.hpp>
#include <lexy/input/buffer.hpp>

#include <clauf/assert.hpp>

//=== types ===//
namespace clauf
{
enum class native_specifier
{
    none,
    default_,
    string,
};

enum class type_node_kind
{
    builtin_type,
    pointer_type,
    array_type,
    function_type,
    qualified_type,
    decl_type,
};

/// The base class of all C types in the AST.
using type      = dryad::node<type_node_kind>;
using type_list = dryad::unlinked_node_list<type>;

/// A builtin type like int.
class builtin_type : public dryad::basic_node<type_node_kind::builtin_type, type>
{
public:
    enum type_kind_t : std::uint16_t
    {
        void_,
        nullptr_t,

        // Unsigned character type char.
        char_,

        sint8,
        uint8,
        sint16,
        uint16,
        sint32,
        uint32,
        sint64,
        uint64,
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

/// A pointer type.
class pointer_type
: public dryad::basic_node<type_node_kind::pointer_type, dryad::container_node<type>>
{
public:
    explicit pointer_type(dryad::node_ctor ctor, native_specifier native, type* pointee_type)
    : node_base(ctor), _native(native)
    {
        insert_child_after(nullptr, pointee_type);
    }

    DRYAD_CHILD_NODE_GETTER(type, pointee_type, nullptr)

    native_specifier native() const
    {
        return _native;
    }

private:
    native_specifier _native;
};

/// An array type.
class array_type : public dryad::basic_node<type_node_kind::array_type, dryad::container_node<type>>
{
public:
    explicit array_type(dryad::node_ctor ctor, type* element_type, std::size_t size)
    : node_base(ctor), _size(size)
    {
        insert_child_after(nullptr, element_type);
    }

    DRYAD_CHILD_NODE_GETTER(type, element_type, nullptr)

    bool is_incomplete() const
    {
        return _size == 0;
    }

    std::size_t size() const
    {
        return _size;
    }

private:
    std::size_t _size;
};

/// A function type like int(void).
class function_type
: public dryad::basic_node<type_node_kind::function_type, dryad::container_node<type>>
{
public:
    explicit function_type(dryad::node_ctor ctor, type* return_type, type_list parameters)
    : node_base(ctor)
    {
        insert_child_after(nullptr, return_type);
        insert_child_list_after(return_type, parameters);
    }

    DRYAD_CHILD_NODE_GETTER(type, return_type, nullptr)
    DRYAD_CHILD_NODE_RANGE_GETTER(type, parameters, return_type(), this)
};

/// A type with a cv qualifier.
class qualified_type
: public dryad::basic_node<type_node_kind::qualified_type, dryad::container_node<type>>
{
public:
    enum qualifier_t : std::uint16_t
    {
        unqualified = 0,
        const_      = 1 << 0,
        volatile_   = 1 << 1,
        restrict_   = 1 << 2,

        const_volatile = const_ | volatile_,
    };

    explicit qualified_type(dryad::node_ctor ctor, int quals, clauf::type* child) : node_base(ctor)
    {
        set_qualifiers_impl(qualifier_t(quals));
        insert_child_after(nullptr, child);
    }

    qualifier_t qualifiers() const
    {
        return qualifiers_impl();
    }

    DRYAD_CHILD_NODE_GETTER(type, unqualified_type, nullptr)

private:
    DRYAD_ATTRIBUTE_USER_DATA16(qualifier_t, qualifiers_impl);
};

class decl;

/// The type created by a declaration.
class decl_type : public dryad::basic_node<type_node_kind::decl_type, type>
{
public:
    explicit decl_type(dryad::node_ctor ctor, const clauf::decl* d) : node_base(ctor), _decl(d) {}

    const clauf::decl* decl() const
    {
        return _decl;
    }

private:
    const clauf::decl* _decl;
};

struct type_hasher : dryad::node_hasher_base<type_hasher, builtin_type, pointer_type, array_type,
                                             function_type, qualified_type, decl_type>
{
    template <typename HashAlgorithm>
    static void hash(HashAlgorithm& hasher, const builtin_type* n)
    {
        hasher.hash_scalar(n->type_kind());
    }
    template <typename HashAlgorithm>
    static void hash(HashAlgorithm& hasher, builtin_type::type_kind_t kind)
    {
        hasher.hash_scalar(kind);
    }
    template <typename HashAlgorithm>
    static void hash(HashAlgorithm& hasher, const pointer_type* ptr)
    {
        hasher.hash_scalar(ptr->native());
    }
    template <typename HashAlgorithm>
    static void hash(HashAlgorithm& hasher, const array_type* array)
    {
        hasher.hash_scalar(array->size());
    }
    template <typename HashAlgorithm>
    static void hash(HashAlgorithm&, const function_type*)
    {}
    template <typename HashAlgorithm>
    static void hash(HashAlgorithm& hasher, const qualified_type* ty)
    {
        hasher.hash_scalar(ty->qualifiers());
    }
    template <typename HashAlgorithm>
    static void hash(HashAlgorithm& hasher, const decl_type* ty)
    {
        hasher.hash_scalar(ty->decl());
    }

    static bool is_equal(const builtin_type* lhs, const builtin_type* rhs)
    {
        return lhs->type_kind() == rhs->type_kind();
    }
    static bool is_equal(const builtin_type* node, builtin_type::type_kind_t kind)
    {
        return node->type_kind() == kind;
    }
    static bool is_equal(const pointer_type* lhs, const pointer_type* rhs)
    {
        return lhs->native() == rhs->native();
    }
    static bool is_equal(const array_type* lhs, const array_type* rhs)
    {
        return lhs->size() == rhs->size();
    }
    static bool is_equal(const function_type*, const function_type*)
    {
        return true;
    }
    static bool is_equal(const qualified_type* lhs, const qualified_type* rhs)
    {
        return lhs->qualifiers() == rhs->qualifiers();
    }
    static bool is_equal(const decl_type* lhs, const decl_type* rhs)
    {
        return lhs->decl() == rhs->decl();
    }
};
using type_forest = dryad::hash_forest<type, type_hasher>;

type* clone(type_forest::node_creator creator, const type* ty);
type* make_unsigned(type_forest::node_creator creator, const type* ty);

bool is_same(const type* lhs, const type* rhs);
bool is_same_modulo_qualifiers(const type* lhs, const type* rhs);

bool is_void(const type* ty);
bool is_signed_int(const type* ty);
bool is_unsigned_int(const type* ty);
bool is_char(const type* ty);
bool is_integer(const type* ty);
bool is_arithmetic(const type* ty);
bool is_pointer(const type* ty);
bool is_scalar(const type* ty);

bool is_array(const type* ty);

bool is_complete_object_type(const type* ty);
bool is_pointer_to_complete_object_type(const type* ty);

clauf::qualified_type::qualifier_t type_qualifiers_of(const type* ty);
const type*                        unqualified_type_of(const type* ty);

/// Returns -1 for non-integers.
unsigned integer_rank_of(const type* ty);
} // namespace clauf

namespace clauf
{
enum class node_kind
{
    translation_unit,

    //=== expressions ===//
    nullptr_constant_expr,
    integer_constant_expr,
    string_literal_expr,
    type_constant_expr,
    builtin_expr,
    identifier_expr,
    function_call_expr,
    cast_expr,
    decay_expr,
    unary_expr,
    arithmetic_expr,
    comparison_expr,
    sequenced_expr,
    assignment_expr,
    conditional_expr,

    first_expr = nullptr_constant_expr,
    last_expr  = conditional_expr,

    //=== statements ===//
    null_stmt,
    decl_stmt,
    expr_stmt,
    return_stmt,
    break_stmt,
    continue_stmt,
    if_stmt,
    while_stmt,
    block_stmt,

    first_stmt = null_stmt,
    last_stmt  = block_stmt,

    //=== initializers ===//
    empty_init,
    braced_init,
    expr_init,

    first_init = empty_init,
    last_init  = expr_init,

    //=== declarations ===//
    variable_decl,
    parameter_decl,
    member_decl,
    function_decl,
    struct_decl,

    first_decl = variable_decl,
    last_decl  = struct_decl,
};

using node = dryad::node<node_kind>;

struct ast_symbol_id;
using ast_symbol          = dryad::symbol<ast_symbol_id, std::uint32_t>;
using ast_symbol_interner = dryad::symbol_interner<ast_symbol_id, char, std::uint32_t>;

class decl;
using decl_list = dryad::unlinked_node_list<decl>;

class stmt;
using stmt_list = dryad::unlinked_node_list<stmt>;

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

struct name
{
    location   loc;
    ast_symbol symbol;
};

class file
{
public:
    explicit file(const char* path, lexy::buffer<lexy::utf8_char_encoding>&& buffer)
    : _buffer(LEXY_MOV(buffer)), _path(path)
    {}

    const lexy::buffer<lexy::utf8_char_encoding>& buffer() const
    {
        return _buffer;
    }

    const char* path() const noexcept
    {
        return _path;
    }

    void set_location(const node* n, location loc)
    {
        _map.insert(n, loc);
    }

    location location_of(const node* n) const
    {
        auto result = _map.lookup(n);
        CLAUF_ASSERT(result != nullptr, "every node should have a location");
        return *result;
    }

private:
    lexy::buffer<lexy::utf8_char_encoding> _buffer;
    const char*                            _path;
    dryad::node_map<const node, location>  _map;
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
    const clauf::type* type() const
    {
        return _type;
    }

protected:
    explicit expr(dryad::node_ctor ctor, node_kind kind, const clauf::type* type)
    : node_base(ctor, kind), _type(type)
    {}

private:
    const clauf::type* _type;
};

bool is_lvalue(const expr* e);
bool is_modifiable_lvalue(const expr* e);
bool is_static_lvalue(const expr* e);
bool is_lvalue_with_address(const expr* e);

bool is_named_constant(const expr* e);
bool is_arithmetic_constant_expr(const expr* e);
bool is_integer_constant_expr(const expr* e);
bool is_nullptr_constant(const expr* e);
bool is_address_constant(const expr* e);
bool is_address_constant_for_complete_type(const expr* e);
bool is_address_constant_with_offset(const expr* e);
bool is_constant_expr(const expr* e);

using expr_list = dryad::unlinked_node_list<expr>;

class nullptr_constant_expr : public dryad::basic_node<node_kind::nullptr_constant_expr, expr>
{
public:
    explicit nullptr_constant_expr(dryad::node_ctor ctor, const clauf::type* ty)
    : node_base(ctor, ty)
    {
        CLAUF_PRECONDITION(dryad::node_cast<builtin_type>(ty)->type_kind()
                           == builtin_type::nullptr_t);
    }
};

class integer_constant_expr : public dryad::basic_node<node_kind::integer_constant_expr, expr>
{
public:
    explicit integer_constant_expr(dryad::node_ctor ctor, const clauf::type* ty,
                                   std::uint64_t value)
    : node_base(ctor, ty), _value(value)
    {}

    std::uint64_t value() const
    {
        return _value;
    }

private:
    std::uint64_t _value;
};

class string_literal_expr : public dryad::basic_node<node_kind::string_literal_expr, expr>
{
public:
    explicit string_literal_expr(dryad::node_ctor ctor, const clauf::type* ty, const char* value)
    : node_base(ctor, ty), _value(value)
    {}

    const char* value() const
    {
        return _value;
    }

private:
    const char* _value;
};

/// A sizeof or alignof expression.
class type_constant_expr : public dryad::basic_node<node_kind::type_constant_expr, expr>
{
public:
    enum op_t : std::uint16_t
    {
        sizeof_,
        alignof_,
    };

    explicit type_constant_expr(dryad::node_ctor ctor, const clauf::type* ty, op_t op,
                                const clauf::type* operand_ty)
    : node_base(ctor, ty), _type(operand_ty)
    {
        DRYAD_PRECONDITION(dryad::node_cast<builtin_type>(ty)->type_kind() == builtin_type::uint64);
        set_op_impl(op);
    }

    op_t op() const
    {
        return op_impl();
    }

    const clauf::type* operand_type() const
    {
        return _type;
    }

private:
    DRYAD_ATTRIBUTE_USER_DATA16(op_t, op_impl);

    const clauf::type* _type;
};

/// An expression that does a builtin action.
class builtin_expr : public dryad::basic_node<node_kind::builtin_expr, expr>
{
public:
    enum builtin_t : std::uint16_t
    {
        print,
        assert,
        malloc,
        free,
    };

    explicit builtin_expr(dryad::node_ctor ctor, const clauf::type* ty, builtin_t builtin,
                          clauf::expr* expr)
    : node_base(ctor, ty)
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

/// A name, which refers to a declaration, e.g. `int i`
class identifier_expr : public dryad::basic_node<node_kind::identifier_expr, expr>
{
public:
    explicit identifier_expr(dryad::node_ctor ctor, const clauf::type* ty, clauf::decl* decl)
    : node_base(ctor, ty), _decl(decl)
    {}

    clauf::decl* declaration() const
    {
        return _decl;
    }

private:
    clauf::decl* _decl;
};

/// A function call expression.
class function_call_expr : public dryad::basic_node<node_kind::function_call_expr, expr>
{
public:
    explicit function_call_expr(dryad::node_ctor ctor, const clauf::type* type, clauf::expr* fn,
                                expr_list arguments)
    : node_base(ctor, type)
    {
        insert_child_after(nullptr, fn);
        insert_child_list_after(fn, arguments);
    }

    DRYAD_CHILD_NODE_GETTER(expr, function, nullptr)
    DRYAD_CHILD_NODE_RANGE_GETTER(expr, arguments, function(), this)
};

/// A cast expression or implicit conversion.
class cast_expr : public dryad::basic_node<node_kind::cast_expr, expr>
{
public:
    explicit cast_expr(dryad::node_ctor ctor, const clauf::type* target_type, clauf::expr* child)
    : node_base(ctor, target_type)
    {
        insert_child_after(nullptr, child);
    }

    DRYAD_CHILD_NODE_GETTER(expr, child, nullptr)
};

/// An lvalue conversion that converts an lvalue expression into its value,
/// or an array into a pointer to its first element.
class decay_expr : public dryad::basic_node<node_kind::decay_expr, expr>
{
public:
    explicit decay_expr(dryad::node_ctor ctor, const clauf::type* target_type, clauf::expr* child)
    : node_base(ctor, target_type)
    {
        insert_child_after(nullptr, child);
    }

    DRYAD_CHILD_NODE_GETTER(expr, child, nullptr)

    bool is_array_decay_conversion() const
    {
        return !clauf::is_same(this->type(), child()->type());
    }
};

enum class unary_op : std::uint16_t
{
    plus, // +
    neg,  // -
    bnot, // ~
    lnot, // !

    pre_inc,  // ++tmp
    pre_dec,  // --tmp
    post_inc, // tmp++
    post_dec, // tmp--

    address, // &
    deref,   // *
};

/// A unary expression.
class unary_expr : public dryad::basic_node<node_kind::unary_expr, expr>
{
public:
    explicit unary_expr(dryad::node_ctor ctor, const clauf::type* type, unary_op op,
                        clauf::expr* child)
    : node_base(ctor, type)
    {
        set_op_impl(op);
        insert_child_after(nullptr, child);
    }

    unary_op op() const
    {
        return op_impl();
    }

    DRYAD_CHILD_NODE_GETTER(clauf::expr, child, nullptr)

private:
    DRYAD_ATTRIBUTE_USER_DATA16(unary_op, op_impl);
};

template <node_kind Kind, typename OpT>
class binary_expr : public dryad::basic_node<Kind, expr>
{
public:
    explicit binary_expr(dryad::node_ctor ctor, const clauf::type* type, OpT op, clauf::expr* left,
                         clauf::expr* right)
    : dryad::basic_node<Kind, expr>(ctor, type)
    {
        this->user_data16() = std::uint16_t(op);
        this->insert_children_after(nullptr, left, right);
    }

    OpT op() const
    {
        return OpT(this->user_data16());
    }

    DRYAD_CHILD_NODE_GETTER(expr, left, nullptr)
    DRYAD_CHILD_NODE_GETTER(expr, right, left())

private:
    using dryad::basic_node<Kind, expr>::user_data16;
};

enum class arithmetic_op : std::uint16_t
{
    add,
    sub,
    ptrdiff, // subtraction ptr - ptr
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

/// Assignment expression.
using assignment_expr = binary_expr<node_kind::assignment_expr, assignment_op>;

class conditional_expr : public dryad::basic_node<node_kind::conditional_expr, expr>
{
public:
    explicit conditional_expr(dryad::node_ctor ctor, const clauf::type* type,
                              clauf::expr* condition, clauf::expr* if_true, clauf::expr* if_false)
    : node_base(ctor, type)
    {
        insert_children_after(nullptr, condition, if_true, if_false);
    }

    DRYAD_CHILD_NODE_GETTER(expr, condition, nullptr)
    DRYAD_CHILD_NODE_GETTER(expr, if_true, condition())
    DRYAD_CHILD_NODE_GETTER(expr, if_false, if_true())
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

/// A statement that does nothing.
class null_stmt : public dryad::basic_node<node_kind::null_stmt, stmt>
{
public:
    explicit null_stmt(dryad::node_ctor ctor) : node_base(ctor) {}
};

/// A statement that declares (multiple) things e.g. `int i, j;`
class decl_stmt : public dryad::basic_node<node_kind::decl_stmt, stmt>
{
public:
    explicit decl_stmt(dryad::node_ctor ctor, decl_list decls) : node_base(ctor)
    {
        insert_child_list_after(nullptr, decls);
    }

    DRYAD_CHILD_NODE_RANGE_GETTER(decl, declarations, nullptr, this)
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

/// A return statement, e.g. `return 0;`
class return_stmt : public dryad::basic_node<node_kind::return_stmt, stmt>
{
public:
    explicit return_stmt(dryad::node_ctor ctor) : node_base(ctor) {}
    explicit return_stmt(dryad::node_ctor ctor, clauf::expr* expr) : node_base(ctor)
    {
        insert_child_after(nullptr, expr);
    }

    DRYAD_CHILD_NODE_GETTER(clauf::expr, expr, nullptr)
};

/// A break statement.
class break_stmt : public dryad::basic_node<node_kind::break_stmt, stmt>
{
public:
    DRYAD_NODE_CTOR(break_stmt)
};

/// A continue statement.
class continue_stmt : public dryad::basic_node<node_kind::continue_stmt, stmt>
{
public:
    DRYAD_NODE_CTOR(continue_stmt)
};

/// An if statement.
class if_stmt : public dryad::basic_node<node_kind::if_stmt, stmt>
{
public:
    explicit if_stmt(dryad::node_ctor ctor, clauf::expr* condition, clauf::stmt* then)
    : node_base(ctor)
    {
        insert_children_after(nullptr, condition, then);
    }
    explicit if_stmt(dryad::node_ctor ctor, clauf::expr* condition, clauf::stmt* then,
                     clauf::stmt* else_)
    : node_base(ctor)
    {
        insert_children_after(nullptr, condition, then, else_);
    }

    DRYAD_CHILD_NODE_GETTER(clauf::expr, condition, nullptr)
    DRYAD_CHILD_NODE_GETTER(clauf::stmt, then, condition())

    bool has_else() const
    {
        return node_after(then()) != this;
    }

    DRYAD_CHILD_NODE_GETTER(clauf::stmt, else_, then())
};

/// A while statement.
class while_stmt : public dryad::basic_node<node_kind::while_stmt, stmt>
{
public:
    enum loop_kind_t : std::uint16_t
    {
        loop_while,
        loop_do_while,
    };

    explicit while_stmt(dryad::node_ctor ctor, loop_kind_t kind, clauf::expr* condition,
                        clauf::stmt* body)
    : node_base(ctor)
    {
        insert_children_after(nullptr, condition, body);
        set_loop_kind_impl(kind);
    }
    explicit while_stmt(dryad::node_ctor ctor, loop_kind_t kind, clauf::stmt* body,
                        clauf::expr* condition)
    : while_stmt(ctor, kind, condition, body)
    {}

    DRYAD_CHILD_NODE_GETTER(clauf::expr, condition, nullptr)
    DRYAD_CHILD_NODE_GETTER(clauf::stmt, body, condition())

    loop_kind_t loop_kind() const
    {
        return loop_kind_impl();
    }

private:
    DRYAD_ATTRIBUTE_USER_DATA16(loop_kind_t, loop_kind_impl);
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

//=== initializers ===//
namespace clauf
{
/// The initializer of a declaration.
class init : public dryad::abstract_node_range<node, node_kind::first_init, node_kind::last_init>
{
protected:
    DRYAD_ABSTRACT_NODE_CTOR(init)
};

/// The empty initializer.
class empty_init : public dryad::basic_node<node_kind::empty_init, init>
{
public:
    DRYAD_NODE_CTOR(empty_init)
};

/// A braced initializer.
class braced_init : public dryad::basic_node<node_kind::braced_init, dryad::container_node<init>>
{
public:
    braced_init(dryad::node_ctor ctor, dryad::unlinked_node_list<init> initializers)
    : node_base(ctor)
    {
        this->insert_child_list_after(nullptr, initializers);
    }

    DRYAD_CHILD_NODE_RANGE_GETTER(init, initializers, nullptr, this)

    std::size_t trailing_empty_inits() const
    {
        return _trailing_empty_inits;
    }
    void set_trailing_empty_inits(std::size_t n)
    {
        _trailing_empty_inits = n;
    }

private:
    std::size_t _trailing_empty_inits = 0;
};

/// An expression initializer.
class expr_init : public dryad::basic_node<node_kind::expr_init, dryad::container_node<init>>
{
public:
    expr_init(dryad::node_ctor ctor, expr* e) : node_base(ctor), _expr(e) {}

    expr* expression()
    {
        return _expr;
    }
    const expr* expression() const
    {
        return _expr;
    }

    void set_expression(expr* e)
    {
        _expr = e;
    }

    // Adds the expression as a child; it can now longer be changed.
    // This needs to be called after all implicit conversions have been handled.
    void freeze_expression()
    {
        this->insert_child_after(nullptr, _expr);
    }

private:
    expr* _expr;
};

bool is_constant_init(const init* init);

std::size_t initializer_count_of(const init* init);
} // namespace clauf

//=== declaration ===//
namespace clauf
{
enum class linkage : std::uint16_t
{
    none,
    external,
    internal,
    native,
};

/// The baseclass of all declarations in the AST.
class decl : public dryad::abstract_node_range<dryad::container_node<node>, node_kind::first_decl,
                                               node_kind::last_decl>
{
public:
    ast_symbol name() const
    {
        return _name;
    }

    const clauf::type* type() const
    {
        return _type;
    }

    clauf::linkage linkage() const
    {
        return linkage_impl();
    }

    bool is_definition() const
    {
        return _definition == this;
    }
    bool has_definition() const
    {
        return _definition != nullptr;
    }

    clauf::decl* definition() const
    {
        return _definition;
    }

    void make_definition()
    {
        _definition = this;
    }
    void set_definition(clauf::decl* def)
    {
        _definition = def;
    }

protected:
    explicit decl(dryad::node_ctor ctor, node_kind kind, ast_symbol name, const clauf::type* type)
    : node_base(ctor, kind), _name(name), _type(type), _definition(nullptr)
    {
        set_linkage_impl(clauf::linkage::none);
    }

    DRYAD_ATTRIBUTE_USER_DATA16(clauf::linkage, linkage_impl);

private:
    ast_symbol         _name;
    const clauf::type* _type;
    clauf::decl*       _definition;
};

enum class storage_duration : std::uint8_t
{
    static_,
    automatic,
    register_,
};

/// A variable declaration.
class variable_decl : public dryad::basic_node<node_kind::variable_decl, decl>
{
public:
    explicit variable_decl(dryad::node_ctor ctor, clauf::linkage linkage, ast_symbol name,
                           storage_duration sd, bool is_constexpr, const clauf::type* type,
                           clauf::init* initializer = nullptr)
    : node_base(ctor, name, type), _sd(sd), _constexpr(is_constexpr)
    {
        set_linkage_impl(linkage);
        if (initializer != nullptr)
            insert_child_after(nullptr, initializer);
    }

    bool has_initializer() const
    {
        return first_child() != nullptr;
    }
    void set_initializer(clauf::init* initializer)
    {
        CLAUF_PRECONDITION(!has_initializer());
        insert_child_after(nullptr, initializer);
    }
    DRYAD_CHILD_NODE_GETTER(clauf::init, initializer, nullptr)

    bool is_constexpr() const
    {
        return _constexpr;
    }
    clauf::storage_duration storage_duration() const
    {
        return _sd;
    }

    variable_decl* definition() const
    {
        return dryad::node_cast<variable_decl>(decl::definition());
    }
    void set_definition(variable_decl* def)
    {
        decl::set_definition(def);
    }

private:
    clauf::storage_duration _sd;
    bool                    _constexpr;
};

/// A parameter declaration.
class parameter_decl : public dryad::basic_node<node_kind::parameter_decl, decl>
{
public:
    explicit parameter_decl(dryad::node_ctor ctor, ast_symbol name, const clauf::type* type)
    : node_base(ctor, name, type)
    {}
};

using parameter_list = dryad::unlinked_node_list<parameter_decl>;

/// A member declaration.
class member_decl : public dryad::basic_node<node_kind::member_decl, decl>
{
public:
    explicit member_decl(dryad::node_ctor ctor, ast_symbol name, const clauf::type* type)
    : node_base(ctor, name, type)
    {}
};

using member_list = dryad::unlinked_node_list<member_decl>;

/// A function declaration.
class function_decl : public dryad::basic_node<node_kind::function_decl, decl>
{
public:
    explicit function_decl(dryad::node_ctor ctor, clauf::linkage linkage, ast_symbol name,
                           const clauf::type* type, parameter_list params)
    : node_base(ctor, name, type)
    {
        set_linkage_impl(linkage);
        insert_child_list_after(nullptr, params);
        if (params.empty())
            _last_param = nullptr;
        else
            _last_param = params.back();
    }

    DRYAD_CHILD_NODE_RANGE_GETTER(parameter_decl, parameters, nullptr,
                                  this->node_after(_last_param))
    DRYAD_CHILD_NODE_GETTER(clauf::block_stmt, body, _last_param)

    const clauf::function_type* type() const
    {
        return dryad::node_cast<clauf::function_type>(decl::type());
    }

    void set_body(clauf::block_stmt* block)
    {
        insert_child_after(_last_param, block);
    }

    function_decl* definition() const
    {
        return dryad::node_cast<function_decl>(decl::definition());
    }
    void set_definition(function_decl* def)
    {
        decl::set_definition(def);
    }

private:
    node* _last_param;
};

/// A struct declaration.
class struct_decl : public dryad::basic_node<node_kind::struct_decl, decl>
{
public:
    explicit struct_decl(dryad::node_ctor ctor, ast_symbol name, type_forest& types,
                         member_list members)
    : node_base(ctor, name, types.create<clauf::decl_type>(this))
    {
        insert_child_list_after(nullptr, members);
    }

    DRYAD_CHILD_NODE_RANGE_GETTER(member_decl, members, nullptr, this)
};
} // namespace clauf

//=== declarator tree ===//
namespace clauf
{
enum class declarator_kind
{
    name,
    array,
    function,
    pointer,

    init,
};

using declarator      = dryad::node<declarator_kind>;
using declarator_list = dryad::unlinked_node_list<declarator>;

class name_declarator : public dryad::basic_node<declarator_kind::name>
{
public:
    explicit name_declarator(dryad::node_ctor ctor, clauf::name name) : node_base(ctor), _name(name)
    {}

    clauf::name name() const
    {
        return _name;
    }

private:
    clauf::name _name;
};

class array_declarator
: public dryad::basic_node<declarator_kind::array, dryad::container_node<declarator>>
{
public:
    explicit array_declarator(dryad::node_ctor ctor, declarator* child, std::size_t size)
    : node_base(ctor), _size(size)
    {
        insert_child_after(nullptr, child);
    }

    DRYAD_CHILD_NODE_GETTER(declarator, child, nullptr)

    std::size_t size() const
    {
        return _size;
    }

private:
    std::size_t _size;
};

class function_declarator
: public dryad::basic_node<declarator_kind::function, dryad::container_node<declarator>>
{
public:
    explicit function_declarator(dryad::node_ctor ctor, declarator* child,
                                 parameter_list parameters)
    : node_base(ctor), _parameters(parameters)
    {
        insert_child_after(nullptr, child);
    }

    DRYAD_CHILD_NODE_GETTER(declarator, child, nullptr)

    parameter_list parameters() const
    {
        return _parameters;
    }

private:
    parameter_list _parameters;
};

class pointer_declarator
: public dryad::basic_node<declarator_kind::pointer, dryad::container_node<declarator>>
{
public:
    explicit pointer_declarator(dryad::node_ctor ctor, clauf::qualified_type::qualifier_t quals,
                                declarator* child)
    : node_base(ctor)
    {
        set_qualifiers_impl(quals);
        insert_child_after(nullptr, child);
    }

    DRYAD_CHILD_NODE_GETTER(declarator, child, nullptr)

    clauf::qualified_type::qualifier_t qualifiers() const
    {
        return qualifiers_impl();
    }

private:
    DRYAD_ATTRIBUTE_USER_DATA16(clauf::qualified_type::qualifier_t, qualifiers_impl);
};

class init_declarator
: public dryad::basic_node<declarator_kind::init, dryad::container_node<declarator>>
{
public:
    explicit init_declarator(dryad::node_ctor ctor, declarator* child, init* initializer)
    : node_base(ctor), _init(initializer)
    {
        insert_child_after(nullptr, child);
    }

    DRYAD_CHILD_NODE_GETTER(declarator, child, nullptr)

    init* initializer() const
    {
        return _init;
    }

private:
    init* _init;
};

name        get_name(const declarator* decl);
init*       get_init(const declarator* decl);
const type* get_type(type_forest& types, const declarator* decl, native_specifier native,
                     const type* decl_type);
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

    void add_structs(dryad::unlinked_node_list<clauf::struct_decl> decls)
    {
        insert_child_list_after(nullptr, decls);
    }

    DRYAD_CHILD_NODE_RANGE_GETTER(decl, declarations, nullptr, this)
};

/// The entire AST of a source file.
struct ast
{
    file                          input;
    ast_symbol_interner           symbols;
    dryad::tree<translation_unit> tree;
    type_forest                   types;

    explicit ast(file&& input) : input(LEXY_MOV(input)) {}

    translation_unit* root()
    {
        return tree.root();
    }
    const translation_unit* root() const
    {
        return tree.root();
    }

    template <typename T, typename... Args>
    auto create(location loc, Args&&... args) -> std::enable_if_t<dryad::is_node<T, node_kind>, T*>
    {
        auto node = tree.template create<T>(DRYAD_FWD(args)...);
        input.set_location(node, loc);
        return node;
    }
    template <typename T, typename... Args>
    auto create(Args&&... args) -> std::enable_if_t<dryad::is_node<T, type_node_kind>, T*>
    {
        return dryad::node_cast<T>(types.template create<T>(DRYAD_FWD(args)...));
    }
    builtin_type* create(builtin_type::type_kind_t kind)
    {
        return dryad::node_cast<builtin_type>(types.lookup_or_create<builtin_type>(kind));
    }
};

void dump_type(const ast_symbol_interner& symbols, const clauf::type* ty);
void dump_ast(const ast& ast);
} // namespace clauf

#endif // CLAUF_AST_HPP_INCLUDED

