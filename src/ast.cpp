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
        [&](const clauf::array_type* ty) -> clauf::type* {
            return creator.create<clauf::array_type>(clone(creator, ty->element_type()),
                                                     ty->size());
        },
        [&](const clauf::function_type* ty) -> clauf::type* {
            clauf::type_list params;
            for (auto param : ty->parameters())
                params.push_back(clone(creator, param));

            return creator.create<clauf::function_type>(clone(creator, ty->return_type()), params);
        },
        [&](const clauf::qualified_type* ty) -> clauf::type* {
            auto unqual_ty = clone(creator, ty->unqualified_type());
            return creator.create<clauf::qualified_type>(ty->qualifiers(), unqual_ty);
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

bool clauf::is_same_modulo_qualifiers(const type* lhs, const type* rhs)
{
    if (clauf::is_same(lhs, rhs))
        return true;

    if (auto qualified_lhs = dryad::node_try_cast<clauf::qualified_type>(lhs))
        return clauf::is_same_modulo_qualifiers(qualified_lhs->unqualified_type(), rhs);
    else if (auto qualified_rhs = dryad::node_try_cast<clauf::qualified_type>(rhs))
        return clauf::is_same_modulo_qualifiers(lhs, qualified_rhs->unqualified_type());
    else
        return false;
}

bool clauf::is_void(const type* ty_)
{
    auto ty = clauf::unqualified_type_of(ty_);
    if (auto builtin = dryad::node_try_cast<clauf::builtin_type>(ty))
        return builtin->type_kind() == clauf::builtin_type::void_;
    else
        return false;
}

bool clauf::is_signed_int(const type* ty_)
{
    auto ty      = clauf::unqualified_type_of(ty_);
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
bool clauf::is_unsigned_int(const type* ty_)
{
    auto ty      = clauf::unqualified_type_of(ty_);
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

bool clauf::is_pointer(const type* ty_)
{
    auto ty = clauf::unqualified_type_of(ty_);
    return dryad::node_has_kind<clauf::pointer_type>(ty);
}

bool clauf::is_scalar(const type* ty)
{
    return clauf::is_arithmetic(ty) || clauf::is_pointer(ty);
}

bool clauf::is_array(const type* ty_)
{
    auto ty = clauf::unqualified_type_of(ty_);
    return dryad::node_has_kind<clauf::array_type>(ty);
}

bool clauf::is_complete_object_type(const type* ty_)
{
    auto ty = clauf::unqualified_type_of(ty_);
    if (dryad::node_has_kind<clauf::function_type>(ty))
        return false;

    return !clauf::is_void(ty);
}

bool clauf::is_pointer_to_complete_object_type(const type* ty_)
{
    auto ty = clauf::unqualified_type_of(ty_);
    if (!clauf::is_pointer(ty))
        return false;

    return clauf::is_complete_object_type(
        dryad::node_cast<clauf::pointer_type>(ty)->pointee_type());
}

clauf::qualified_type::qualifier_t clauf::type_qualifiers_of(const type* ty)
{
    if (auto qualified = dryad::node_try_cast<clauf::qualified_type>(ty))
        return qualified->qualifiers();
    else
        return clauf::qualified_type::unqualified;
}
const clauf::type* clauf::unqualified_type_of(const type* ty)
{
    if (auto qualified = dryad::node_try_cast<clauf::qualified_type>(ty))
        return qualified->unqualified_type();
    else
        return ty;
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
    return is_lvalue(e) && is_complete_object_type(e->type())
           && (type_qualifiers_of(e->type()) & clauf::qualified_type::const_) == 0;
}

bool clauf::is_lvalue_with_address(const expr* e)
{
    if (auto id = dryad::node_try_cast<clauf::identifier_expr>(e))
    {
        if (auto var = dryad::node_try_cast<clauf::variable_decl>(id->declaration()))
            return var->storage_duration() != clauf::storage_duration::register_;

        return true;
    }
    else if (auto unary = dryad::node_try_cast<clauf::unary_expr>(e))
        return unary->op() == clauf::unary_op::deref;
    else
        return false;
}

bool clauf::is_static_lvalue(const expr* e)
{
    if (auto id = dryad::node_try_cast<identifier_expr>(e))
    {
        if (auto var = dryad::node_try_cast<variable_decl>(id->declaration()))
            return var->storage_duration() == clauf::storage_duration::static_;
        else if (dryad::node_has_kind<function_decl>(id->declaration()))
            return true;
    }

    return false;
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

bool clauf::is_named_constant(const expr* e)
{
    if (auto id = dryad::node_try_cast<identifier_expr>(e))
    {
        if (auto var = dryad::node_try_cast<variable_decl>(id->declaration()))
            return var->is_constexpr();
        else if (dryad::node_has_kind<function_decl>(id->declaration()))
            return true;
    }

    return false;
}

bool clauf::is_arithmetic_constant_expr(const expr* e)
{
    if (!is_arithmetic(e->type()))
        return false;

    return dryad::visit_node_all(
        e, [](const nullptr_constant_expr*) { return false; },
        [](const integer_constant_expr*) { return true; },
        [](const type_constant_expr*) { return true; }, [](const builtin_expr*) { return false; },
        [](const identifier_expr* e) { return is_named_constant(e); },
        [](const function_call_expr*) { return false; },
        [](const cast_expr* e) { return is_arithmetic_constant_expr(e->child()); },
        [](const unary_expr* e) {
            switch (e->op())
            {
            case unary_op::plus:
            case unary_op::neg:
            case unary_op::bnot:
            case unary_op::lnot:
                break;

            case unary_op::pre_inc:
            case unary_op::pre_dec:
            case unary_op::post_inc:
            case unary_op::post_dec:
                // These ones are explicitly called out in the standard.
            case unary_op::address:
                // &foo does not have arithmetic type, so can't be an arithmetic constant expr.
            case unary_op::deref:
                // For *foo the operand does not have arithmetic type, so it can't be an arithmetic
                // constant expr.
                return false;
            }

            return is_arithmetic_constant_expr(e->child());
        },
        [](const arithmetic_expr* e) {
            return is_arithmetic_constant_expr(e->left())
                   && is_arithmetic_constant_expr(e->right());
        },
        [](const comparison_expr* e) {
            return is_arithmetic_constant_expr(e->left())
                   && is_arithmetic_constant_expr(e->right());
        },
        [](const sequenced_expr* e) {
            switch (e->op())
            {
            case sequenced_op::land:
            case sequenced_op::lor:
                break;
            case sequenced_op::comma:
                return false;
            }
            return is_arithmetic_constant_expr(e->left())
                   && is_arithmetic_constant_expr(e->right());
        },
        [](const assignment_expr*) { return false; },
        [](const conditional_expr* e) {
            return is_arithmetic_constant_expr(e->condition())
                   && is_arithmetic_constant_expr(e->if_true())
                   && is_arithmetic_constant_expr(e->if_false());
        });
}

bool clauf::is_integer_constant_expr(const expr* e)
{
    // Integer constant expression are arithmetic constant expressions of integer type, except for
    // the following edge case where floating point numbers have to be the immediate operand of a
    // cast:
    // * integer constant expr: (int)3.14
    // * not an integer constant expr: (int)(3.14 + 1)
    //
    // We're not bothering to check that for now, since we don't have float anyway.
    return is_arithmetic_constant_expr(e) && is_integer(e->type());
}

bool clauf::is_address_constant(const expr* e)
{
    if (is_nullptr_constant(e))
        return true;
    else if (auto unary = dryad::node_try_cast<unary_expr>(e))
        return unary->op() == unary_op::address && is_static_lvalue(unary->child());
    else if (auto cast = dryad::node_try_cast<cast_expr>(e))
        return is_pointer(cast->type()) && is_integer_constant_expr(cast->child());
    else
        // TODO: expression of array or function type are address constant
        return false;
}

bool clauf::is_address_constant_for_complete_type(const expr* e)
{
    if (!is_address_constant(e))
        return false;

    auto type = e->type();
    if (!is_pointer(type))
        // Address constant for nullptr.
        return false;

    auto pointer = dryad::node_cast<pointer_type>(unqualified_type_of(type));
    return is_complete_object_type(pointer->pointee_type());
}

bool clauf::is_address_constant_with_offset(const expr* e)
{
    if (auto arithmetic = dryad::node_try_cast<arithmetic_expr>(e))
    {
        if (arithmetic->op() != arithmetic_op::add && arithmetic->op() != arithmetic_op::sub)
            return false;

        return (is_address_constant_for_complete_type(arithmetic->left())
                && is_integer_constant_expr(arithmetic->right()))
               || (is_address_constant_for_complete_type(arithmetic->right())
                   && is_integer_constant_expr(arithmetic->left()));
    }

    return false;
}

bool clauf::is_constant_expr(const expr* e)
{
    return is_named_constant(e) || is_arithmetic_constant_expr(e) || is_address_constant(e)
           || is_address_constant_with_offset(e);
}

clauf::name clauf::get_name(const declarator* decl)
{
    return dryad::visit_node_all(
        decl, [](const name_declarator* decl) { return decl->name(); },
        [](const array_declarator* decl) { return get_name(decl->child()); },
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
                clauf::type* result
                    = creator.create<clauf::pointer_type>(clauf::clone(creator, child_type));
                if (decl->qualifiers() != clauf::qualified_type::unqualified)
                    result = creator.create<clauf::qualified_type>(decl->qualifiers(), result);
                return result;
            });
        },
        [&](const clauf::array_declarator* decl) {
            auto child_type = get_type(types, decl->child(), decl_type);
            return types.build([&](clauf::type_forest::node_creator creator) {
                return creator.create<clauf::array_type>(clauf::clone(creator, child_type),
                                                         decl->size());
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
    case clauf::node_kind::type_constant_expr:
        return "type constant expr";
    case clauf::node_kind::builtin_expr:
        return "builtin expr";
    case clauf::node_kind::identifier_expr:
        return "identifier expr";
    case clauf::node_kind::function_call_expr:
        return "function call expr";
    case clauf::node_kind::decay_expr:
        return "decay expr";
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

} // namespace

void clauf::dump_type(const clauf::type* ty)
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
        [](dryad::traverse_event_enter, const clauf::array_type* ty) {
            std::printf("[%zu] ", ty->size());
        },
        [](dryad::child_visitor<clauf::type_node_kind> visitor, const clauf::function_type* ty) {
            std::printf("(");
            for (auto param : ty->parameters())
                visitor(param);
            std::printf(") -> ");
            visitor(ty->return_type());
        },
        [](dryad::traverse_event_enter, const clauf::qualified_type* ty) {
            if ((ty->qualifiers() & clauf::qualified_type::const_) != 0)
                std::printf("const ");
            if ((ty->qualifiers() & clauf::qualified_type::volatile_) != 0)
                std::printf("volatile ");
            if ((ty->qualifiers() & clauf::qualified_type::restrict_) != 0)
                std::printf("restrict ");
        });
}

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
            [&](const type_constant_expr* expr) {
                switch (expr->op())
                {
                case type_constant_expr::sizeof_:
                    std::printf("sizeof ");
                    break;
                case type_constant_expr::alignof_:
                    std::printf("alignof ");
                    break;
                }
                dump_type(expr->operand_type());
            },
            [&](const builtin_expr* expr) {
                switch (expr->builtin())
                {
                case builtin_expr::print:
                    std::printf("__clauf_print");
                    break;
                case builtin_expr::assert:
                    std::printf("__clauf_assert");
                    break;
                case builtin_expr::malloc:
                    std::printf("__clauf_malloc");
                    break;
                case builtin_expr::free:
                    std::printf("__clauf_free");
                    break;
                }
            },
            [&](const identifier_expr* expr) {
                std::printf("'%s' : ", expr->declaration()->name().c_str(ast.symbols));
                dump_type(expr->type());
            },
            [&](const cast_expr* expr) { dump_type(expr->type()); },
            [&](const decay_expr* expr) { dump_type(expr->type()); },
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
                    break;
                case unary_op::deref:
                    std::printf("*");
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
                case arithmetic_op::ptrdiff:
                    std::printf("- (ptr)");
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
                switch (d->linkage())
                {
                case linkage::none:
                    break;
                case linkage::external:
                    std::printf("external ");
                    break;
                case linkage::internal:
                    std::printf("internal ");
                    break;
                }
                std::printf("'%s' : ", d->name().c_str(ast.symbols));
                dump_type(d->type());

                if (auto var = dryad::node_try_cast<variable_decl>(d))
                {
                    switch (var->storage_duration())
                    {
                    case storage_duration::static_:
                        std::printf(" [static]");
                        break;
                    case storage_duration::automatic:
                        break;
                    case storage_duration::register_:
                        std::printf(" [register]");
                        break;
                    }

                    if (var->is_constexpr())
                        std::printf(" [constexpr]");
                }

                if (!d->has_definition())
                    std::printf(" [no definition]");
                else if (d->is_definition())
                    std::printf(" [definition]");
            });

        std::putchar('\n');
        if (ev == dryad::traverse_event::enter)
            ++level;
    }
}

