// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <clauf/compiler.hpp>

#include <dryad/symbol_table.hpp>
#include <lexy/action/parse.hpp>
#include <lexy/callback.hpp>
#include <lexy/dsl.hpp>
#include <optional>
#include <string>
#include <vector>

#include <clauf/assert.hpp>
#include <clauf/ast.hpp>
#include <clauf/diagnostic.hpp>

namespace
{
struct scope
{
    enum kind_t
    {
        // The global scope of the translation unit.
        global,
        // The local scope inside a function. Local scopes can be nested.
        local,
        // The local scope of an if statement.
        local_if,
        // The local scope of a loop; here break and continue is allowed.
        local_loop,
    } kind;
    dryad::symbol_table<clauf::ast_symbol, clauf::decl*> symbols;
    scope*                                               parent;

    scope(kind_t kind, scope* parent) : kind(kind), parent(parent) {}
};

struct compiler_state
{
    clauf::diagnostic_logger       logger;
    clauf::ast                     ast;
    dryad::tree<clauf::declarator> decl_tree;

    scope                 global_scope;
    scope*                current_scope;
    clauf::function_decl* current_function = nullptr;

    int symbol_generator_count;

    compiler_state(const clauf::file& input)
    : logger(input), global_scope(scope::global, nullptr), current_scope(&global_scope),
      symbol_generator_count(0)
    {}

    clauf::ast_symbol generate_symbol()
    {
        auto str = std::string("__clauf_anon_") + std::to_string(symbol_generator_count);
        ++symbol_generator_count;
        return ast.symbols.intern(str.c_str(), str.size());
    }
};

void insert_new_decl(compiler_state& state, clauf::decl* decl)
{
    if (state.current_scope->kind != scope::local && state.current_scope->kind != scope::global)
    {
        state.logger.log(clauf::diagnostic_kind::error, "declaration not allowed in this scope")
            .annotation(clauf::annotation_kind::primary, state.ast.location_of(decl), "here")
            .finish();
    }

    auto shadowed = state.current_scope->symbols.insert_or_shadow(decl->name(), decl);
    if (shadowed != nullptr)
    {
        auto name = decl->name().c_str(state.ast.symbols);
        state.logger
            .log(clauf::diagnostic_kind::error, "duplicate %s declaration '%s'",
                 state.current_scope->kind == scope::global ? "global" : "local", name)
            .annotation(clauf::annotation_kind::secondary, state.ast.location_of(shadowed),
                        "first declaration")
            .annotation(clauf::annotation_kind::primary, state.ast.location_of(decl),
                        "second declaration")
            .finish();
    }
}

void check_inside_loop(compiler_state& state, clauf::location loc)
{
    auto inside_loop = false;
    for (auto scope = state.current_scope; scope != nullptr; scope = scope->parent)
        if (scope->kind == scope::local_loop)
        {
            inside_loop = true;
            break;
        }

    if (!inside_loop)
    {
        state.logger.log(clauf::diagnostic_kind::error, "cannot use break/continue outside loop")
            .annotation(clauf::annotation_kind::primary, loc, "here")
            .finish();
    }
}

// Attempts to convert the value expression to target_type by creating a cast_expr or raising an
// error.
clauf::expr* do_assignment_conversion(compiler_state& state, clauf::location loc,
                                      clauf::assignment_op op, const clauf::type* target_type,
                                      clauf::expr* value)
{
    if (clauf::is_same(target_type, value->type()))
        return value;

    if ((clauf::is_arithmetic(target_type) && clauf::is_arithmetic(value->type()))
        || (clauf::is_pointer(target_type) && clauf::is_nullptr_constant(value)))
    {
        return state.ast.create<clauf::cast_expr>(loc, target_type, value);
    }
    else if (clauf::is_pointer(target_type) && clauf::is_pointer(value->type()))
    {
        auto target_pointee_type
            = dryad::node_cast<clauf::pointer_type>(target_type)->pointee_type();
        auto value_pointee_type
            = dryad::node_cast<clauf::pointer_type>(value->type())->pointee_type();
        if (clauf::is_void(target_pointee_type) || clauf::is_void(value_pointee_type))
            return state.ast.create<clauf::cast_expr>(loc, target_type, value);
    }
    else if (clauf::is_pointer(target_type) && clauf::is_integer(value->type())
             && (op == clauf::assignment_op::add || op == clauf::assignment_op::sub))
        return value;

    state.logger.log(clauf::diagnostic_kind::error, "cannot do implicit conversion in assignment")
        .annotation(clauf::annotation_kind::primary, loc, "here")
        .finish();
    return value;
}

// Performs integer promotion.
clauf::expr* do_integer_promotion(compiler_state& state, clauf::location loc, clauf::expr* expr)
{
    if (!clauf::is_integer(expr->type()))
        return expr;

    auto target_type = [&]() -> const clauf::type* {
        auto kind = dryad::node_cast<clauf::builtin_type>(expr->type())->type_kind();
        switch (kind)
        {
        case clauf::builtin_type::void_:
        case clauf::builtin_type::nullptr_t:
            CLAUF_UNREACHABLE("not an integer");
            return nullptr;

        case clauf::builtin_type::sint8:
        case clauf::builtin_type::uint8:
        case clauf::builtin_type::sint16:
        case clauf::builtin_type::uint16:
        case clauf::builtin_type::sint32:
        case clauf::builtin_type::uint32:
            return state.ast.create(clauf::builtin_type::sint64);

        case clauf::builtin_type::sint64:
        case clauf::builtin_type::uint64:
            return expr->type();
        }
    }();
    if (clauf::is_same(target_type, expr->type()))
        return expr;

    return state.ast.create<clauf::cast_expr>(loc, target_type, expr);
}

// Performs the usual arithmetic conversions on both operands.
const clauf::type* do_usual_arithmetic_conversions(compiler_state& state, clauf::location loc,
                                                   clauf::expr*& lhs, clauf::expr*& rhs)
{
    CLAUF_PRECONDITION(clauf::is_integer(lhs->type()) && clauf::is_integer(rhs->type()));

    lhs = do_integer_promotion(state, loc, lhs);
    rhs = do_integer_promotion(state, loc, rhs);
    if (clauf::is_same(lhs->type(), rhs->type()))
        return lhs->type();

    if (clauf::is_signed_int(lhs->type()) == clauf::is_signed_int(rhs->type()))
    {
        auto rank_lhs = clauf::integer_rank_of(lhs->type());
        auto rank_rhs = clauf::integer_rank_of(rhs->type());
        if (rank_lhs > rank_rhs)
            rhs = state.ast.create<clauf::cast_expr>(loc, lhs->type(), rhs);
        else
            lhs = state.ast.create<clauf::cast_expr>(loc, rhs->type(), lhs);
    }
    else
    {
        auto& signed_op   = clauf::is_signed_int(lhs->type()) ? lhs : rhs;
        auto& unsigned_op = clauf::is_unsigned_int(lhs->type()) ? lhs : rhs;

        auto signed_rank   = clauf::integer_rank_of(signed_op->type());
        auto unsigned_rank = clauf::integer_rank_of(unsigned_op->type());
        if (unsigned_rank >= signed_rank)
        {
            signed_op = state.ast.create<clauf::cast_expr>(loc, unsigned_op->type(), signed_op);
        }
        // Since the rank is the number of bits, this compares the value range.
        else if (signed_rank > unsigned_rank)
        {
            unsigned_op = state.ast.create<clauf::cast_expr>(loc, signed_op->type(), unsigned_op);
        }
        else
        {
            auto target_type = state.ast.types.build(
                [&](auto creator) { return clauf::make_unsigned(creator, signed_op->type()); });
            signed_op   = state.ast.create<clauf::cast_expr>(loc, target_type, signed_op);
            unsigned_op = state.ast.create<clauf::cast_expr>(loc, target_type, unsigned_op);
        }
    }

    // We have adjusted both operands to return the same type at this point, so just return it.
    return lhs->type();
}

template <typename ReturnType, typename... Callback>
constexpr auto callback(Callback... cb)
{
    return lexy::bind(lexy::callback<ReturnType>(cb...), lexy::parse_state, lexy::values);
}
template <typename T>
constexpr auto construct = callback<T*>(
    [](compiler_state& state, clauf::location loc, auto&& arg) {
        if constexpr (std::is_same_v<std::decay_t<decltype(arg)>, lexy::nullopt>)
            return state.ast.create<T>(loc);
        else
            return state.ast.create<T>(loc, DRYAD_FWD(arg));
    },
    [](compiler_state& state, clauf::location loc, auto&&... args) {
        return state.ast.create<T>(loc, DRYAD_FWD(args)...);
    });
} // namespace

namespace clauf::grammar
{
namespace dsl = lexy::dsl;

constexpr auto id = dsl::identifier(dsl::unicode::xid_start_underscore, dsl::unicode::xid_continue);

constexpr auto kw_nullptr  = LEXY_KEYWORD("nullptr", id);
constexpr auto kw_return   = LEXY_KEYWORD("return", id);
constexpr auto kw_break    = LEXY_KEYWORD("break", id);
constexpr auto kw_continue = LEXY_KEYWORD("continue", id);
constexpr auto kw_if       = LEXY_KEYWORD("if", id);
constexpr auto kw_else     = LEXY_KEYWORD("else", id);
constexpr auto kw_while    = LEXY_KEYWORD("while", id);
constexpr auto kw_do       = LEXY_KEYWORD("do", id);

constexpr auto kw_type_ops = lexy::symbol_table<clauf::type_constant_expr::op_t> //
                                 .map(LEXY_LIT("sizeof"), clauf::type_constant_expr::sizeof_)
                                 .map(LEXY_LIT("alignof"), clauf::type_constant_expr::alignof_);

constexpr auto kw_type_specifiers = lexy::symbol_table<clauf::type_specifier> //
                                        .map(LEXY_LIT("void"), clauf::type_specifier::void_)
                                        .map(LEXY_LIT("int"), clauf::type_specifier::int_)
                                        .map(LEXY_LIT("char"), clauf::type_specifier::char_)
                                        .map(LEXY_LIT("signed"), clauf::type_specifier::signed_)
                                        .map(LEXY_LIT("unsigned"), clauf::type_specifier::unsigned_)
                                        .map(LEXY_LIT("short"), clauf::type_specifier::short_);

constexpr auto kw_builtin_exprs = lexy::symbol_table<clauf::builtin_expr::builtin_t> //
                                      .map(LEXY_LIT("__clauf_print"), clauf::builtin_expr::print)
                                      .map(LEXY_LIT("__clauf_assert"), clauf::builtin_expr::assert)
                                      .map(LEXY_LIT("__clauf_malloc"), clauf::builtin_expr::malloc)
                                      .map(LEXY_LIT("__clauf_free"), clauf::builtin_expr::free);

template <bool AllowReserved>
struct identifier
{
    static constexpr auto name = "identifier";

    static constexpr auto rule
        = id.reserve(kw_nullptr, dsl::literal_set(kw_type_ops), kw_return, kw_break, kw_continue,
                     kw_if, kw_else, kw_while, kw_do, dsl::literal_set(kw_type_specifiers),
                     dsl::literal_set(kw_builtin_exprs));
    static constexpr auto value = callback<clauf::name>([](compiler_state& state, auto lexeme) {
        auto symbol = state.ast.symbols.intern(lexeme.data(), lexeme.size());

        if constexpr (!AllowReserved)
        {
            auto symbol_str = std::string_view(symbol.c_str(state.ast.symbols));

            if (symbol_str.find("__") != std::string_view::npos
                || (symbol_str.size() >= 2 && symbol_str[0] == '_' && std::isupper(symbol_str[1]))
                || (state.current_scope->kind == scope::global && symbol_str[0] == '_'))
            {
                state.logger
                    .log(clauf::diagnostic_kind::warning, "identifier '%s' is reserved",
                         symbol_str.data())
                    .annotation(clauf::annotation_kind::primary, {lexeme.begin(), lexeme.end()},
                                "used as declaration name here")
                    .finish();
            }
        }

        return clauf::name{{lexeme.begin(), lexeme.end()}, symbol};
    });
};
} // namespace clauf::grammar

//=== expression parsing ===//
namespace clauf::grammar
{
template <typename Enum = std::nullptr_t>
struct op_tag
{
    clauf::location loc;
    Enum            op;

    op_tag(clauf::location loc, Enum op) : loc(loc), op(op) {}

    operator Enum()
    {
        return op;
    }
};
template <auto Enum>
struct op_tag_for : op_tag<DRYAD_DECAY_DECLTYPE(Enum)>
{
    op_tag_for(const char* pos) : op_tag<DRYAD_DECAY_DECLTYPE(Enum)>(pos, Enum) {}
};

template <auto Enum = nullptr, typename Rule>
constexpr auto op_(Rule rule)
{
    return dsl::op<op_tag_for<Enum>>(rule);
}
} // namespace clauf::grammar

namespace clauf::grammar
{
struct unary_expr;
struct assignment_expr;

struct nullptr_constant_expr
{
    static constexpr auto rule = dsl::position(kw_nullptr);
    static constexpr auto value
        = callback<clauf::nullptr_constant_expr*>([](compiler_state& state, const char* pos) {
              auto type = state.ast.create(clauf::builtin_type::nullptr_t);
              return state.ast.create<clauf::nullptr_constant_expr>(pos, type);
          });
};

struct integer_constant_expr
{
    template <typename Base>
    static constexpr auto integer
        = dsl::integer<std::uint64_t>(dsl::digits<Base>.sep(dsl::digit_sep_tick));

    enum suffix
    {
        none,
        unsigned_,
    };

    static constexpr auto suffixes
        = lexy::symbol_table<suffix>.map<'u'>(suffix::unsigned_).map<'U'>(suffix::unsigned_);

    static constexpr auto rule = [] {
        auto decimal_digits = integer<dsl::decimal>;
        auto octal_digits   = integer<dsl::octal>;
        auto hex_digits     = (LEXY_LIT("0x") | LEXY_LIT("0X")) >> integer<dsl::hex>;
        auto binary_digits  = (LEXY_LIT("0b") | LEXY_LIT("0B")) >> integer<dsl::binary>;

        auto opt_suffix = dsl::opt(dsl::symbol<suffixes>);

        return dsl::peek(dsl::lit_c<'0'>)
                   >> dsl::position + (hex_digits | binary_digits | octal_digits) + opt_suffix
               | dsl::else_ >> dsl::position(decimal_digits) + opt_suffix;
    }();

    static constexpr auto value
        = callback<clauf::integer_constant_expr*>([](compiler_state& state, clauf::location loc,
                                                     std::uint64_t value, std::optional<suffix> s) {
              auto type = s == suffix::unsigned_
                              ? state.ast.create<clauf::builtin_type>(clauf::builtin_type::uint64)
                              : state.ast.create<clauf::builtin_type>(clauf::builtin_type::sint64);
              return state.ast.create<clauf::integer_constant_expr>(loc, type, value);
          });
};

struct identifier_expr
{
    static constexpr auto rule = dsl::p<identifier<true>>;

    static constexpr auto value
        = callback<clauf::identifier_expr*>([](compiler_state& state, clauf::name name) {
              clauf::decl* decl = nullptr;
              for (auto scope = state.current_scope; scope != nullptr; scope = scope->parent)
              {
                  decl = scope->symbols.lookup(name.symbol);
                  if (decl != nullptr)
                      break;
              }

              if (decl == nullptr)
              {
                  auto str = name.symbol.c_str(state.ast.symbols);
                  state.logger.log(diagnostic_kind::error, "unknown identifier '%s'", str)
                      .annotation(annotation_kind::primary, name.loc, "used here")
                      .finish();
              }

              return state.ast.create<clauf::identifier_expr>(name.loc, decl->type(), decl);
          });
};

struct argument_list
{
    static constexpr auto rule = dsl::terminator(LEXY_LIT(")"))
                                     .opt_list(dsl::recurse<assignment_expr>, dsl::sep(dsl::comma));
    static constexpr auto value = lexy::as_list<clauf::expr_list>;
};

template <bool Abstract = false>
struct declarator;
struct type_specifier_list;

// Parses a type name followed by a closing paren.
struct type_name_in_parens
{
    static constexpr auto rule = [] {
        auto type_specifiers = dsl::recurse_branch<type_specifier_list>;
        auto opt_declarator
            = dsl::parenthesized.close()
              | dsl::else_ >> dsl::recurse<declarator<true>> + dsl::parenthesized.close();

        return type_specifiers >> opt_declarator;
    }();
    static constexpr auto value = callback<const clauf::type*>(
        [](compiler_state& state, const clauf::type* base_type, clauf::declarator* decl = nullptr) {
            if (decl != nullptr)
                return clauf::get_type(state.ast.types, decl, base_type);
            else
                return base_type;
        });
};

struct expr;

struct builtin_expr
{
    static constexpr auto rule
        = dsl::position(dsl::symbol<kw_builtin_exprs>) >> dsl::parenthesized(dsl::recurse<expr>);
    static constexpr auto value = callback<clauf::builtin_expr*>(
        [](compiler_state& state, const char* pos, clauf::builtin_expr::builtin_t builtin,
           clauf::expr* child) {
            auto type = [&]() -> const clauf::type* {
                if (builtin == clauf::builtin_expr::malloc)
                    return state.ast.types.build([&](clauf::type_forest::node_creator creator) {
                        auto void_
                            = creator.create<clauf::builtin_type>(clauf::builtin_type::void_);
                        return creator.create<clauf::pointer_type>(void_);
                    });
                else
                {
                    return state.ast.create(clauf::builtin_type::void_);
                }
            }();
            return state.ast.create<clauf::builtin_expr>(pos, type, builtin, child);
        });
};

struct expr : lexy::expression_production
{
    // primary-expression
    static constexpr auto atom
        = [] {
              auto id = dsl::p<identifier_expr>;
              auto constant
                  = dsl::p<nullptr_constant_expr> | dsl::else_ >> dsl::p<integer_constant_expr>;

              // When we have a '(' in the beginning of an expression, it can be either (expr) or
              // (type)expr. This can be distinguished by checking for a type name after the '(',
              // which is not possible if cast were a regular prefix operator.
              //
              // We thus do it here as part of the primary-expression, even though it is not a
              // primary-expression, but has lower precedence. However, no other operator matches
              // before that, so it works out.
              auto cast   = dsl::p<type_name_in_parens> >> dsl::recurse<unary_expr>;
              auto parens = dsl::recurse<expr> + dsl::parenthesized.close();
              auto paren_expr
                  = dsl::position(dsl::parenthesized.open()) >> (cast | dsl::else_ >> parens);

              // sizeof/alignof are technically unary operators, but we can't parse them here since
              // their operand is a type and not an expression. It should make no difference,
              // however.
              //
              // Parse (type-name) or (expr) as operand of sizeof.
              auto type_constant_operand_parens = dsl::parenthesized.open() >>  //
                  (dsl::p<type_name_in_parens> | dsl::else_ >> dsl::recurse<expr> + dsl::parenthesized.close());
              auto type_constant_expr
                  = dsl::position(dsl::symbol<kw_type_ops>)
                    >> (type_constant_operand_parens | dsl::else_ >> dsl::recurse<unary_expr>);

              return paren_expr | type_constant_expr | id
                     | dsl::p<builtin_expr> | dsl::else_ >> constant;
          }();

    struct postfix : dsl::postfix_op
    {
        static constexpr auto op = op_(LEXY_LIT("(") >> dsl::p<argument_list>)
                                   / op_(dsl::square_bracketed(dsl::recurse<expr>))
                                   / op_<clauf::unary_op::post_inc>(LEXY_LIT("++"))
                                   / op_<clauf::unary_op::post_dec>(LEXY_LIT("--"));
        using operand = dsl::atom;
    };

    struct unary : dsl::prefix_op
    {
        static constexpr auto op = op_<clauf::unary_op::plus>(LEXY_LIT("+"))
                                   / op_<clauf::unary_op::neg>(LEXY_LIT("-"))
                                   / op_<clauf::unary_op::bnot>(LEXY_LIT("~"))
                                   / op_<clauf::unary_op::lnot>(LEXY_LIT("!"))
                                   / op_<clauf::unary_op::pre_inc>(LEXY_LIT("++"))
                                   / op_<clauf::unary_op::pre_dec>(LEXY_LIT("--"))
                                   / op_<clauf::unary_op::address>(LEXY_LIT("&"))
                                   / op_<clauf::unary_op::deref>(LEXY_LIT("*"));
        using operand = postfix;
    };

    struct multiplicative : dsl::infix_op_left
    {
        static constexpr auto op = op_<clauf::arithmetic_op::mul>(LEXY_LIT("*"))
                                   / op_<clauf::arithmetic_op::div>(LEXY_LIT("/"))
                                   / op_<clauf::arithmetic_op::rem>(LEXY_LIT("%"));

        // Operand should be cast, but it is handled as part of the atom.
        using operand = unary;
    };

    struct additive : dsl::infix_op_left
    {
        static constexpr auto op = op_<clauf::arithmetic_op::add>(LEXY_LIT("+"))
                                   / op_<clauf::arithmetic_op::sub>(LEXY_LIT("-"));
        using operand = multiplicative;
    };

    struct shift : dsl::infix_op_left
    {
        static constexpr auto op = op_<clauf::arithmetic_op::shl>(LEXY_LIT("<<"))
                                   / op_<clauf::arithmetic_op::shr>(LEXY_LIT(">>"));
        using operand = additive;
    };

    struct relational : dsl::infix_op_left
    {
        static constexpr auto op
            = op_<clauf::comparison_op::lt>(dsl::not_followed_by(LEXY_LIT("<"), LEXY_LIT("<")))
              / op_<clauf::comparison_op::le>(LEXY_LIT("<="))
              / op_<clauf::comparison_op::gt>(dsl::not_followed_by(LEXY_LIT(">"), LEXY_LIT(">")))
              / op_<clauf::comparison_op::ge>(LEXY_LIT(">="));
        using operand = shift;
    };

    struct equality : dsl::infix_op_left
    {
        static constexpr auto op = op_<clauf::comparison_op::eq>(LEXY_LIT("=="))
                                   / op_<clauf::comparison_op::ne>(LEXY_LIT("!="));
        using operand = relational;
    };

    struct band : dsl::infix_op_left
    {
        static constexpr auto op = op_<clauf::arithmetic_op::band>(LEXY_LIT("&"));
        using operand            = equality;
    };
    struct bxor : dsl::infix_op_left
    {
        static constexpr auto op = op_<clauf::arithmetic_op::bxor>(LEXY_LIT("^"));
        using operand            = band;
    };
    struct bor : dsl::infix_op_left
    {
        static constexpr auto op = op_<clauf::arithmetic_op::bor>(LEXY_LIT("|"));
        using operand            = bxor;
    };

    struct land : dsl::infix_op_left
    {
        static constexpr auto op = op_<clauf::sequenced_op::land>(LEXY_LIT("&&"));
        using operand            = bor;
    };
    struct lor : dsl::infix_op_left
    {
        static constexpr auto op = op_<clauf::sequenced_op::lor>(LEXY_LIT("||"));
        using operand            = land;
    };

    struct conditional : dsl::infix_op_right
    {
        static constexpr auto op = op_<0>(LEXY_LIT("?") >> dsl::recurse<expr> + LEXY_LIT(":"));
        using operand            = lor;
    };

    struct assignment : dsl::infix_op_right
    {
        static constexpr auto op
            = op_<clauf::assignment_op::none>(LEXY_LIT("="))
              / op_<assignment_op::add>(LEXY_LIT("+=")) / op_<assignment_op::sub>(LEXY_LIT("-="))
              / op_<assignment_op::mul>(LEXY_LIT("*=")) / op_<assignment_op::div>(LEXY_LIT("/="))
              / op_<assignment_op::rem>(LEXY_LIT("%=")) / op_<assignment_op::band>(LEXY_LIT("&="))
              / op_<assignment_op::bor>(LEXY_LIT("|=")) / op_<assignment_op::bxor>(LEXY_LIT("^="))
              / op_<assignment_op::shl>(LEXY_LIT("<<=")) / op_<assignment_op::shr>(LEXY_LIT(">>="));

        using operand = conditional;
    };

    struct operation : dsl::infix_op_left
    {
        static constexpr auto op = op_<sequenced_op::comma>(dsl::comma);
        using operand            = assignment;
    };

    static clauf::expr* create_unary(compiler_state& state, op_tag<clauf::unary_op> op,
                                     clauf::expr* child)
    {
        auto is_valid_type = [&] {
            switch (op)
            {
            case unary_op::plus:
            case unary_op::neg:
                return clauf::is_arithmetic(child->type());
            case unary_op::bnot:
                return clauf::is_integer(child->type());
            case unary_op::lnot:
                return clauf::is_scalar(child->type());
            case clauf::unary_op::pre_inc:
            case clauf::unary_op::pre_dec:
            case clauf::unary_op::post_inc:
            case clauf::unary_op::post_dec:
                return (clauf::is_arithmetic(child->type())
                        || clauf::is_pointer_to_complete_object_type(child->type()))
                       && clauf::is_modifiable_lvalue(child);
            case clauf::unary_op::address:
                return clauf::is_lvalue(child);
            case clauf::unary_op::deref:
                return clauf::is_pointer(child->type());
            }
        }();
        if (!is_valid_type)
        {
            state.logger.log(clauf::diagnostic_kind::error, "invalid type for unary operator")
                .annotation(clauf::annotation_kind::primary, op.loc, "here")
                .finish();
        }

        if (op == clauf::unary_op::address)
        {
            auto type = state.ast.types.build([&](clauf::type_forest::node_creator creator) {
                return creator.create<clauf::pointer_type>(clauf::clone(creator, child->type()));
            });
            return state.ast.create<clauf::unary_expr>(op.loc, type, op, child);
        }
        else if (op == clauf::unary_op::deref)
        {
            auto type = dryad::node_cast<clauf::pointer_type>(child->type())->pointee_type();
            return state.ast.create<clauf::unary_expr>(op.loc, type, op, child);
        }
        else if (op == clauf::unary_op::lnot)
        {
            // We need to do integer promotion as it's defined in terms of ==, which does integer
            // promotion.
            child     = do_integer_promotion(state, op.loc, child);
            auto type = state.ast.create(clauf::builtin_type::sint64);
            return state.ast.create<clauf::unary_expr>(op.loc, type, op, child);
        }
        else
        {
            // For increment/decrement, we need to do the usual artihmetic conversions between
            // `child` and the number 1. However, if we assume that 1 already has the correct type,
            // this just does integer promotion on `child`, so we can just call that instead.
            //
            // For the other unary operators, integer promotion is what we need to do anyway.
            child = do_integer_promotion(state, op.loc, child);
            return state.ast.create<clauf::unary_expr>(op.loc, child->type(), op, child);
        }
    }

    static constexpr auto value = callback<clauf::expr*>( //
        [](const compiler_state&, clauf::expr* expr) { return expr; },
        [](const compiler_state&, const char*, clauf::expr* expr) { return expr; },
        [](compiler_state& state, const char* pos, clauf::type_constant_expr::op_t op,
           const clauf::type* operand_ty) {
            auto type = state.ast.create(clauf::builtin_type::uint64);
            return state.ast.create<clauf::type_constant_expr>(pos, type, op, operand_ty);
        },
        [](compiler_state& state, const char* pos, clauf::type_constant_expr::op_t op,
           const clauf::expr* operand_expr) {
            if (op != clauf::type_constant_expr::sizeof_)
            {
                state.logger
                    .log(clauf::diagnostic_kind::error,
                         "only sizeof can take an expression directly")
                    .annotation(clauf::annotation_kind::primary,
                                state.ast.location_of(operand_expr), "here")
                    .finish();
            }

            auto type = state.ast.create(clauf::builtin_type::uint64);
            return state.ast.create<clauf::type_constant_expr>(pos, type, op, operand_expr->type());
        },
        [](compiler_state& state, const char* pos, const clauf::type* target_type,
           clauf::expr* child) -> clauf::expr* {
            // Check that the target type is valid.
            if (!clauf::is_scalar(target_type) && !clauf::is_void(target_type))
            {
                state.logger.log(clauf::diagnostic_kind::error, "invalid target type for cast")
                    .annotation(clauf::annotation_kind::primary, pos, "cast here")
                    .finish();
            }

            // Check that we can convert the source type to target type.
            if (clauf::is_void(target_type))
            {
                // All source types allowed.
            }
            else if (clauf::is_arithmetic(target_type))
            {
                if (!clauf::is_arithmetic(child->type()))
                {
                    state.logger.log(clauf::diagnostic_kind::error, "invalid source type for cast")
                        .annotation(clauf::annotation_kind::primary, pos, "cast here")
                        .finish();
                }
            }

            if (clauf::is_same(target_type, child->type()))
                return child;
            else
                return state.ast.create<clauf::cast_expr>(pos, target_type, child);
        },
        [](compiler_state& state, clauf::expr* fn, op_tag<> op, clauf::expr_list arguments) {
            auto fn_type = dryad::node_try_cast<clauf::function_type>(fn->type());
            if (fn_type == nullptr)
            {
                state.logger
                    .log(clauf::diagnostic_kind::error, "called expression is not a function")
                    .annotation(clauf::annotation_kind::primary, state.ast.location_of(fn),
                                "call here")
                    .finish();

                fn_type
                    = state.ast.create<clauf::function_type>(state.ast.create<clauf::builtin_type>(
                                                                 clauf::builtin_type::sint64),
                                                             clauf::type_list());
            }

            clauf::expr_list converted_arguments;
            auto             cur_param = fn_type->parameters().begin();
            auto             end_param = fn_type->parameters().end();
            while (!arguments.empty() && cur_param != end_param)
            {
                auto argument = arguments.pop_front();
                argument      = do_assignment_conversion(state, state.ast.location_of(argument),
                                                         assignment_op::none, *cur_param, argument);
                converted_arguments.push_back(argument);

                ++cur_param;
            }
            if (!arguments.empty() || cur_param != end_param)
            {
                state.logger
                    .log(clauf::diagnostic_kind::error,
                         "mismatched number of parameters and arguments in function call")
                    .annotation(clauf::annotation_kind::primary, state.ast.location_of(fn),
                                "call here")
                    .finish();
            }

            return state.ast.create<clauf::function_call_expr>(op.loc, fn_type->return_type(), fn,
                                                               converted_arguments);
        },
        // This is called for ptr[index]
        [](compiler_state& state, clauf::expr* ptr, op_tag<> op, clauf::expr* index) {
            // Normalize, so pointer is always the left argument.
            if (!clauf::is_pointer(ptr->type()))
                std::swap(ptr, index);

            if (!clauf::is_pointer_to_complete_object_type(ptr->type())
                || !clauf::is_integer(index->type()))
            {
                state.logger
                    .log(clauf::diagnostic_kind::error, "invalid type for subscript operator")
                    .annotation(clauf::annotation_kind::primary, op.loc, "here")
                    .finish();
            }

            auto offset
                = state.ast.create<clauf::arithmetic_expr>(op.loc, ptr->type(),
                                                           clauf::arithmetic_op::add, ptr, index);
            return create_unary(state, {op.loc, clauf::unary_op::deref}, offset);
        },
        [](compiler_state& state, clauf::expr* child, op_tag<clauf::unary_op> op) {
            return create_unary(state, op, child);
        },
        [](compiler_state& state, op_tag<clauf::unary_op> op, clauf::expr* child) {
            return create_unary(state, op, child);
        },
        [](compiler_state& state, clauf::expr* left, op_tag<clauf::arithmetic_op> op,
           clauf::expr* right) {
            const clauf::type* type          = nullptr;
            auto               is_valid_type = [&] {
                switch (op)
                {
                case clauf::arithmetic_op::sub:
                    if (clauf::is_pointer_to_complete_object_type(left->type())
                        && clauf::is_pointer_to_complete_object_type(right->type()))
                    {
                        type  = state.ast.create(clauf::builtin_type::sint64);
                        op.op = clauf::arithmetic_op::ptrdiff;
                        return true;
                    }
                    // fallthrough
                case clauf::arithmetic_op::add:
                    if (clauf::is_pointer_to_complete_object_type(left->type()))
                    {
                        type = left->type();
                        return clauf::is_integer(right->type());
                    }
                    else if (clauf::is_pointer_to_complete_object_type(right->type()))
                    {
                        // We always want the pointer operand on the left.
                        std::swap(left, right);
                        type = left->type();
                        return clauf::is_integer(right->type());
                    }
                    else
                        return clauf::is_arithmetic(left->type())
                               && clauf::is_arithmetic(right->type());

                case clauf::arithmetic_op::mul:
                case clauf::arithmetic_op::div:
                case clauf::arithmetic_op::rem:
                    return clauf::is_arithmetic(left->type())
                           && clauf::is_arithmetic(right->type());
                case clauf::arithmetic_op::band:
                case clauf::arithmetic_op::bor:
                case clauf::arithmetic_op::bxor:
                case clauf::arithmetic_op::shl:
                case clauf::arithmetic_op::shr:
                    return clauf::is_integer(left->type()) && clauf::is_integer(right->type());

                case clauf::arithmetic_op::ptrdiff:
                    CLAUF_UNREACHABLE("not an operator that is parsed");
                    break;
                }
            }();
            if (!is_valid_type)
            {
                state.logger.log(clauf::diagnostic_kind::error, "invalid type for binary operator")
                    .annotation(clauf::annotation_kind::primary, op.loc, "here")
                    .finish();

                type = left->type();
            }
            else
            {
                if (op != clauf::arithmetic_op::shl && op != clauf::arithmetic_op::shr
                    && clauf::is_arithmetic(left->type()) && clauf::is_arithmetic(right->type()))
                {
                    type = do_usual_arithmetic_conversions(state, op.loc, left, right);
                }
            }

            DRYAD_ASSERT(type != nullptr, "type should have been set at some point");
            return state.ast.create<clauf::arithmetic_expr>(op.loc, type, op, left, right);
        },
        [](compiler_state& state, clauf::expr* left, op_tag<clauf::comparison_op> op,
           clauf::expr* right) {
            if (clauf::is_arithmetic(left->type()) && clauf::is_arithmetic(right->type()))
            {
                do_usual_arithmetic_conversions(state, op.loc, left, right);
            }
            else if (clauf::is_pointer(left->type()) || clauf::is_pointer(right->type())
                     || clauf::is_nullptr_constant(left) || clauf::is_nullptr_constant(right))
            {
                // TODO: check for compatible pointer types
                // TODO: prevent nullptr comparison for relational
            }
            else
            {
                state.logger.log(clauf::diagnostic_kind::error, "invalid type for comparison")
                    .annotation(clauf::annotation_kind::primary, op.loc, "here")
                    .finish();
            }

            auto type = state.ast.types.create<clauf::builtin_type>(clauf::builtin_type::sint64);
            return state.ast.create<clauf::comparison_expr>(op.loc, type, op, left, right);
        },
        [](compiler_state& state, clauf::expr* left, op_tag<clauf::sequenced_op> op,
           clauf::expr* right) {
            if (op == clauf::sequenced_op::comma)
            {
                // The type of the comma operator is the type of the right expression.
                return state.ast.create<clauf::sequenced_expr>(op.loc, right->type(), op, left,
                                                               right);
            }
            else
            {
                if (!clauf::is_scalar(left->type()) || !clauf::is_scalar(right->type()))
                {
                    state.logger
                        .log(clauf::diagnostic_kind::error, "invalid type for logical operator")
                        .annotation(clauf::annotation_kind::primary, op.loc, "here")
                        .finish();
                }

                auto type
                    = state.ast.types.create<clauf::builtin_type>(clauf::builtin_type::sint64);
                return state.ast.create<clauf::sequenced_expr>(op.loc, type, op, left, right);
            }
        },
        [](compiler_state& state, clauf::expr* left, op_tag<clauf::assignment_op> op,
           clauf::expr* right) {
            if (!clauf::is_modifiable_lvalue(left))
            {
                state.logger
                    .log(clauf::diagnostic_kind::error,
                         "lhs of assignment is not a modifiable lvalue")
                    .annotation(clauf::annotation_kind::primary, op.loc, "here")
                    .finish();
            }
            right = do_assignment_conversion(state, op.loc, op, left->type(), right);
            return state.ast.create<clauf::assignment_expr>(op.loc, left->type(), op, left, right);
        },
        [](compiler_state& state, clauf::expr* condition, op_tag<int> op, clauf::expr* if_true,
           clauf::expr* if_false) {
            if (!clauf::is_scalar(condition->type()))
            {
                state.logger
                    .log(clauf::diagnostic_kind::error, "invalid type for ternary condition")
                    .annotation(clauf::annotation_kind::primary, op.loc, "here")
                    .finish();
            }

            if (clauf::is_arithmetic(if_true->type()) && clauf::is_arithmetic(if_false->type()))
            {
                do_usual_arithmetic_conversions(state, op.loc, if_true, if_false);
            }
            else if (!clauf::is_same(if_true->type(), if_false->type()))
            {
                state.logger
                    .log(clauf::diagnostic_kind::error,
                         "cannot do implicit conversion between operands")
                    .annotation(clauf::annotation_kind::primary, op.loc, "here")
                    .finish();
            }
            return state.ast.create<clauf::conditional_expr>(op.loc, if_true->type(), condition,
                                                             if_true, if_false);
        });
};

struct unary_expr : lexy::subexpression_production<expr, expr::unary>
{};
struct assignment_expr : lexy::subexpression_production<expr, expr::assignment>
{};
} // namespace clauf::grammar

//=== statement parsing ===//
namespace clauf::grammar
{
struct stmt;
struct declaration;

struct decl_stmt
{
    static constexpr auto rule  = dsl::position(dsl::recurse_branch<declaration>);
    static constexpr auto value = callback<clauf::decl_stmt*>(
        [](compiler_state& state, clauf::location loc, decl_list decls) {
            auto result = state.ast.create<clauf::decl_stmt>(loc, decls);
            for (auto decl : result->declarations())
                insert_new_decl(state, decl);
            return result;
        });
};

struct expr_stmt
{
    static constexpr auto rule  = dsl::position + dsl::p<expr> + dsl::semicolon;
    static constexpr auto value = construct<clauf::expr_stmt>;
};

struct return_stmt
{
    static constexpr auto rule = dsl::position(kw_return)
                                 >> (dsl::semicolon | dsl::else_ >> dsl::p<expr> + dsl::semicolon);
    static constexpr auto value = callback<clauf::return_stmt*>(
        [](compiler_state& state, const char* pos) {
            if (!clauf::is_void(state.current_function->type()->return_type()))
            {
                state.logger
                    .log(clauf::diagnostic_kind::error,
                         "function with non-void return type must have a return value")
                    .annotation(clauf::annotation_kind::secondary,
                                state.ast.location_of(state.current_function),
                                "return type declared here")
                    .annotation(clauf::annotation_kind::primary, pos, "missing return value here")
                    .finish();
            }

            return state.ast.create<clauf::return_stmt>(pos);
        },
        [](compiler_state& state, const char* pos, clauf::expr* expr) {
            expr = do_assignment_conversion(state, pos, assignment_op::none,
                                            state.current_function->type()->return_type(), expr);
            return state.ast.create<clauf::return_stmt>(pos, expr);
        });
};

struct break_stmt
{
    static constexpr auto rule = dsl::capture(kw_break) >> dsl::semicolon;
    static constexpr auto value
        = callback<clauf::break_stmt*>([](compiler_state& state, auto lexeme) {
              check_inside_loop(state, {lexeme.begin(), lexeme.end()});
              return state.ast.create<clauf::break_stmt>(lexeme.begin());
          });
};
struct continue_stmt
{
    static constexpr auto rule = dsl::capture(kw_continue) >> dsl::semicolon;
    static constexpr auto value
        = callback<clauf::continue_stmt*>([](compiler_state& state, auto lexeme) {
              check_inside_loop(state, {lexeme.begin(), lexeme.end()});
              return state.ast.create<clauf::continue_stmt>(lexeme.begin());
          });
};

template <scope::kind_t Kind>
struct secondary_block : lexy::scan_production<clauf::stmt*>
{
    static constexpr auto name = "secondary_block";

    template <typename Context, typename Reader>
    static scan_result scan(lexy::rule_scanner<Context, Reader>& scanner, compiler_state& state)
    {
        scope local_scope(Kind, state.current_scope);
        state.current_scope = &local_scope;

        scan_result result;
        scanner.parse(result, dsl::recurse<stmt>);

        state.current_scope = state.current_scope->parent;
        return result;
    }
};

struct if_stmt
{
    static constexpr auto rule
        = dsl::position(kw_if)
          >> dsl::parenthesized(dsl::p<expr>) + dsl::p<secondary_block<scope::local_if>> //
                 + dsl::if_(kw_else >> dsl::recurse<secondary_block<scope::local_if>>);
    static constexpr auto value = construct<clauf::if_stmt>;
};

struct while_stmt
{
    struct prefix
    {
        static constexpr auto rule  = kw_while;
        static constexpr auto value = lexy::constant(clauf::while_stmt::loop_while);
    };

    static constexpr auto rule
        = dsl::position(dsl::p<prefix>)
          >> dsl::parenthesized(dsl::p<expr>) + dsl::p<secondary_block<scope::local_loop>>;
    static constexpr auto value = construct<clauf::while_stmt>;
};

struct do_while_stmt
{
    struct prefix
    {
        static constexpr auto rule  = kw_do;
        static constexpr auto value = lexy::constant(clauf::while_stmt::loop_do_while);
    };

    static constexpr auto rule
        = dsl::position(dsl::p<prefix>) >> dsl::p<secondary_block<scope::local_loop>> + kw_while
                                               + dsl::parenthesized(dsl::p<expr>) + dsl::semicolon;
    static constexpr auto value = construct<clauf::while_stmt>;
};

struct block_stmt : lexy::scan_production<clauf::block_stmt*>
{
    struct impl
    {
        static constexpr auto rule
            = dsl::position(dsl::curly_bracketed.opt_list(dsl::recurse<stmt>));
        static constexpr auto value = lexy::as_list<stmt_list> >> construct<clauf::block_stmt>;
    };

    static constexpr auto rule = dsl::peek(dsl::lit_c<'{'>) >> dsl::scan;

    template <typename Context, typename Reader>
    static scan_result scan(lexy::rule_scanner<Context, Reader>& scanner, compiler_state& state)
    {
        scope local_scope(scope::local, state.current_scope);
        state.current_scope = &local_scope;

        auto result = scanner.parse(impl{});

        state.current_scope = state.current_scope->parent;
        return result;
    }
};

struct stmt
{
    static constexpr auto rule
        = dsl::p<block_stmt>                                                 //
          | dsl::p<return_stmt> | dsl::p<break_stmt> | dsl::p<continue_stmt> //
          | dsl::p<if_stmt>                                                  //
          | dsl::p<while_stmt> | dsl::p<do_while_stmt>                       //
          | dsl::p<decl_stmt> | dsl::else_ >> dsl::p<expr_stmt>;
    static constexpr auto value = lexy::forward<clauf::stmt*>;
};
} // namespace clauf::grammar

//=== declaration ===//
namespace clauf::grammar
{
struct parameter_list;

struct type_specifier_list
{
    static constexpr auto rule = dsl::position(dsl::list(dsl::symbol<kw_type_specifiers>));
    static constexpr auto value
        = lexy::as_list<std::vector<clauf::type_specifier>> >> callback<clauf::type*>(
              [](compiler_state& state, const char* pos,
                 std::vector<clauf::type_specifier>&& specifiers) -> clauf::type* {
                  std::optional<clauf::builtin_type::type_kind_t> base_type;
                  std::optional<bool>                             is_signed;
                  int                                             short_count = 0;

                  auto log_error = [&] {
                      state.logger
                          .log(clauf::diagnostic_kind::error,
                               "invalid combination of type specifiers")
                          .annotation(clauf::annotation_kind::primary, pos, "here")
                          .finish();
                  };

                  for (auto specifier : specifiers)
                      switch (specifier)
                      {
                      case clauf::type_specifier::void_:
                          if (base_type.has_value())
                              log_error();
                          base_type = clauf::builtin_type::void_;
                          break;
                      case clauf::type_specifier::int_:
                          if (base_type.has_value())
                              log_error();
                          base_type = clauf::builtin_type::sint64;
                          break;
                      case clauf::type_specifier::char_:
                          if (base_type.has_value())
                              log_error();
                          // TODO: set base type to char, not signed char
                          base_type = clauf::builtin_type::sint8;
                          break;

                      case clauf::type_specifier::signed_:
                          if (is_signed.has_value())
                              log_error();
                          is_signed = true;
                          break;
                      case clauf::type_specifier::unsigned_:
                          if (is_signed.has_value())
                              log_error();
                          is_signed = false;
                          break;
                      case clauf::type_specifier::short_:
                          if (short_count == 2)
                              log_error();
                          ++short_count;
                          break;
                      }

                  switch (base_type.value_or(clauf::builtin_type::sint64))
                  {
                  case builtin_type::void_:
                      if (is_signed.has_value())
                          log_error();

                      return state.ast.types.lookup_or_create<clauf::builtin_type>(
                          clauf::builtin_type::void_);

                  case builtin_type::sint8:
                      if (short_count > 0)
                          log_error();

                      if (is_signed.value_or(true))
                          return state.ast.create(clauf::builtin_type::sint8);
                      else
                          return state.ast.create(clauf::builtin_type::uint8);

                  case builtin_type::sint64:
                      if (is_signed.value_or(true))
                      {
                          if (short_count == 0)
                              return state.ast.create(clauf::builtin_type::sint64);
                          else if (short_count == 1)
                              return state.ast.create(clauf::builtin_type::sint32);
                          else
                              return state.ast.create(clauf::builtin_type::sint16);
                      }
                      else
                      {
                          if (short_count == 0)
                              return state.ast.create(clauf::builtin_type::uint64);
                          else if (short_count == 1)
                              return state.ast.create(clauf::builtin_type::uint32);
                          else
                              return state.ast.create(clauf::builtin_type::uint16);
                      }

                  default:
                      CLAUF_UNREACHABLE("not a base type");
                      return nullptr;
                  }
              });
};

template <bool Abstract>
struct declarator : lexy::expression_production
{
    static constexpr auto name = Abstract ? "abstract_declarator" : "declarator";

    static constexpr auto atom = dsl::parenthesized(dsl::recurse<declarator<Abstract>>)
                                 | dsl::p<grammar::identifier<false>> | dsl::else_ >> dsl::position;

    struct pointer_declarator : dsl::prefix_op
    {
        static constexpr auto op = dsl::op<pointer_declarator>(dsl::lit_c<'*'>);
        using operand            = dsl::atom;
    };

    struct function_declarator : dsl::postfix_op
    {
        static constexpr auto op
            = dsl::op<function_declarator>(LEXY_LIT("(") >> dsl::recurse<parameter_list>);
        using operand = pointer_declarator;
    };

    using operation = function_declarator;

    static constexpr auto value = callback<clauf::declarator*>( //
        [](const compiler_state&, clauf::declarator* decl) { return decl; },
        [](compiler_state& state, const char* pos) {
            if (!Abstract)
            {
                state.logger.log(clauf::diagnostic_kind::error, "declaration requires a name")
                    .annotation(clauf::annotation_kind::primary, pos, "here")
                    .finish();
            }

            return state.decl_tree.create<clauf::name_declarator>(
                clauf::name{pos, state.generate_symbol()});
        },
        [](compiler_state& state, clauf::name name) {
            return state.decl_tree.create<clauf::name_declarator>(name);
        },
        [](compiler_state& state, clauf::declarator* child, function_declarator,
           clauf::parameter_list params) {
            return state.decl_tree.create<clauf::function_declarator>(child, params);
        },
        [](compiler_state& state, pointer_declarator, clauf::declarator* child) {
            return state.decl_tree.create<clauf::pointer_declarator>(child);
        });
};

struct parameter_decl
{
    static constexpr auto rule  = dsl::p<type_specifier_list> + dsl::p<declarator<true>>;
    static constexpr auto value = callback<clauf::parameter_decl*>(
        [](compiler_state& state, clauf::type* base_type, clauf::declarator* decl) {
            auto name = get_name(decl);
            auto type = get_type(state.ast.types, decl, base_type);
            if (!clauf::is_complete_object_type(type))
            {
                state.logger
                    .log(clauf::diagnostic_kind::error, "invalid use of incomplete object type")
                    .annotation(clauf::annotation_kind::primary, name.loc,
                                "used to declare parameter here")
                    .finish();
            }
            return state.ast.create<clauf::parameter_decl>(name.loc, name.symbol, type);
        });
};
struct parameter_list
{
    static constexpr auto rule
        = dsl::terminator(LEXY_LIT(")")).opt_list(dsl::p<parameter_decl>, dsl::sep(dsl::comma));
    static constexpr auto value = lexy::as_list<clauf::parameter_list>;
};

struct init_declarator
{
    static constexpr auto rule = dsl::p<declarator<>> //
                                 + dsl::if_(dsl::equal_sign >> dsl::p<assignment_expr>);
    static constexpr auto value = callback<clauf::declarator*>( //
        [](compiler_state&, clauf::declarator* decl) { return decl; },
        [](compiler_state& state, clauf::declarator* decl, clauf::expr* expr) {
            return state.decl_tree.create<clauf::init_declarator>(decl, expr);
        });
};
struct init_declarator_list
{
    static constexpr auto rule  = dsl::list(dsl::p<init_declarator>, dsl::sep(dsl::comma));
    static constexpr auto value = lexy::as_list<clauf::declarator_list>;
};

struct declaration
{
    static constexpr auto rule
        = dsl::p<type_specifier_list> >> dsl::p<init_declarator_list> + dsl::semicolon;

    static clauf::decl* create_non_init_declaration(compiler_state& state, clauf::type* decl_type,
                                                    const clauf::declarator* declarator)
    {
        auto name = get_name(declarator);
        auto type = get_type(state.ast.types, declarator, decl_type);

        return dryad::visit_node_all(
            declarator,
            [&](const clauf::name_declarator*) -> clauf::decl* {
                if (!clauf::is_complete_object_type(type))
                {
                    state.logger
                        .log(clauf::diagnostic_kind::error, "invalid use of incomplete object type")
                        .annotation(clauf::annotation_kind::primary, name.loc,
                                    "used to declare variable here")
                        .finish();
                }

                return state.ast.create<clauf::variable_decl>(name.loc, name.symbol, type);
            },
            [&](const clauf::pointer_declarator*) -> clauf::decl* {
                return state.ast.create<clauf::variable_decl>(name.loc, name.symbol, type);
            },
            [&](const clauf::function_declarator* decl) -> clauf::decl* {
                return state.ast.create<clauf::function_decl>(name.loc, name.symbol, type,
                                                              decl->parameters());
            });
    }

    static constexpr auto value
        = callback<clauf::decl_list>([](compiler_state& state, clauf::type* decl_type,
                                        const clauf::declarator_list& declarators) {
              clauf::decl_list result;
              for (auto declarator : declarators)
              {
                  if (auto init = dryad::node_try_cast<clauf::init_declarator>(declarator))
                  {
                      auto decl     = create_non_init_declaration(state, decl_type, init->child());
                      auto var_decl = dryad::node_cast<clauf::variable_decl>(decl);
                      auto converted_init
                          = do_assignment_conversion(state, state.ast.location_of(decl),
                                                     assignment_op::none, decl->type(),
                                                     init->initializer());
                      var_decl->set_initializer(converted_init);
                      result.push_back(decl);
                  }
                  else
                  {
                      result.push_back(create_non_init_declaration(state, decl_type, declarator));
                  }
              }
              return result;
          });
};

struct global_declaration : lexy::scan_production<clauf::decl_list>
{
    template <typename Context, typename Reader>
    static scan_result scan(lexy::rule_scanner<Context, Reader>& scanner, compiler_state& state)
    {
        auto decl_type = scanner.parse(grammar::type_specifier_list{});
        if (!decl_type)
            return lexy::scan_failed;

        auto decl_list = scanner.parse(grammar::init_declarator_list{});
        if (!decl_list)
            return lexy::scan_failed;

        // At this point, look whether we have a {.
        if (scanner.peek(dsl::lit_c<'{'>))
        {
            // We're having a function definition.
            if (!decl_list.value().has_single_element())
            {
                auto builder
                    = state.logger.log(clauf::diagnostic_kind::error,
                                       "multiple declarators not allowed in function definition");

                auto first = true;
                for (auto decl : decl_list.value())
                {
                    auto name = get_name(decl);
                    (void)builder.annotation(first ? clauf::annotation_kind::primary
                                                   : clauf::annotation_kind::secondary,
                                             name.loc, "declarator");
                    first = false;
                }

                builder.finish();
            }

            auto decl = dryad::node_try_cast<clauf::function_declarator>(decl_list.value().front());
            if (decl == nullptr)
            {
                state.logger
                    .log(clauf::diagnostic_kind::error, "only functions can have a definition")
                    .annotation(clauf::annotation_kind::primary,
                                get_name(decl_list.value().front()).loc, "declarator")
                    .finish();
            }

            auto name = get_name(decl);
            auto type = get_type(state.ast.types, decl, decl_type.value());

            auto existing_decl = state.current_scope->symbols.lookup(name.symbol);
            auto fn_decl = existing_decl ? dryad::node_try_cast<clauf::function_decl>(existing_decl)
                                         : nullptr;
            if (fn_decl != nullptr)
            {
                // TODO: verify that definition matches declaration
            }
            else
            {
                fn_decl = state.ast.create<clauf::function_decl>(name.loc, name.symbol, type,
                                                                 decl->parameters());
                insert_new_decl(state, fn_decl);
            }

            state.current_function = fn_decl;
            scope local_scope(scope::local, state.current_scope);
            state.current_scope = &local_scope;
            for (auto param : fn_decl->parameters())
                insert_new_decl(state, param);

            auto body = scanner.parse(grammar::block_stmt{});
            if (!body)
                return lexy::scan_failed;
            fn_decl->set_body(body.value());

            state.current_scope    = state.current_scope->parent;
            state.current_function = nullptr;
            return fn_decl->is_linked_in_tree() ? nullptr : fn_decl;
        }
        else
        {
            // We're having a declaration that isn't a function definition.
            scanner.parse(dsl::semicolon);
            if (!scanner)
                return lexy::scan_failed;

            auto result = grammar::declaration::value[state](decl_type.value(), decl_list.value());
            for (auto decl : result)
                insert_new_decl(state, decl);
            return result;
        }
    }
};
} // namespace clauf::grammar

//=== translation unit ===//
namespace clauf::grammar
{
struct translation_unit
{
    static constexpr auto whitespace = dsl::ascii::space
                                       | LEXY_LIT("//") >> dsl::until(dsl::newline)
                                       | LEXY_LIT("/*") >> dsl::until(LEXY_LIT("*/"));

    static constexpr auto rule
        = dsl::position + dsl::terminator(dsl::eof).list(dsl::p<global_declaration>);
    static constexpr auto value
        = lexy::concat<clauf::decl_list> >> construct<clauf::translation_unit>;
};
} // namespace clauf::grammar

std::optional<clauf::ast> clauf::compile(file&& input)
{
    compiler_state state(input);
    auto           result = lexy::parse<clauf::grammar::translation_unit>(input.buffer, state,
                                                                state.logger.error_callback());
    if (!result || !state.logger)
        return std::nullopt;

    state.ast.tree.set_root(result.value());
    state.ast.input = std::move(input);
    return std::move(state.ast);
}

