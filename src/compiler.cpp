// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <clauf/compiler.hpp>

#include <dryad/symbol_table.hpp>
#include <lexy/action/parse.hpp>
#include <lexy/callback.hpp>
#include <lexy/dsl.hpp>

#include <clauf/assert.hpp>
#include <clauf/ast.hpp>
#include <clauf/diagnostic.hpp>

//=== declarator tree ===//
namespace clauf
{
enum class declarator_kind
{
    name,
    function,
};

using declarator      = dryad::node<declarator_kind>;
using declarator_list = dryad::unlinked_node_list<declarator>;

struct name
{
    location   loc;
    ast_symbol symbol;
};

struct name_declarator : dryad::basic_node<declarator_kind::name>
{
    clauf::name name;

    explicit name_declarator(dryad::node_ctor ctor, clauf::name name) : node_base(ctor), name(name)
    {}
};

struct function_declarator
: dryad::basic_node<declarator_kind::function, dryad::container_node<declarator>>
{
    location       loc;
    parameter_list parameters;

    explicit function_declarator(dryad::node_ctor ctor, location loc, declarator* child,
                                 parameter_list parameters)
    : node_base(ctor), loc(loc), parameters(parameters)
    {
        insert_child_after(nullptr, child);
    }

    DRYAD_CHILD_NODE_GETTER(declarator, child, nullptr)
};

name get_name(const declarator* decl)
{
    return dryad::visit_node_all(
        decl, [](const name_declarator* decl) { return decl->name; },
        [](const function_declarator* decl) { return get_name(decl->child()); });
}
} // namespace clauf

namespace
{
struct compiler_state
{
    clauf::diagnostic_logger                             logger;
    clauf::ast                                           ast;
    dryad::tree<clauf::declarator_kind>                  decl_tree;
    dryad::symbol_table<clauf::ast_symbol, clauf::decl*> global_symbols;
    dryad::symbol_table<clauf::ast_symbol, clauf::decl*> local_symbols;

    compiler_state(const clauf::file& input) : logger(input) {}
};

clauf::type* clone_type(compiler_state& state, const clauf::type* type)
{
    return dryad::visit_node_all(
        type,
        [&](const clauf::builtin_type* type) -> clauf::type* {
            return state.ast.create<clauf::builtin_type>({}, type->type_kind());
        },
        [&](const clauf::function_type* type) -> clauf::type* {
            clauf::type_list param_types;
            for (auto param : type->parameters())
                param_types.push_back(clone_type(state, param));
            return state.ast.create<clauf::function_type>({},
                                                          clone_type(state, type->return_type()),
                                                          param_types);
        });
}

void insert_new_decl(compiler_state&                                       state,
                     dryad::symbol_table<clauf::ast_symbol, clauf::decl*>& symbol_table,
                     clauf::decl* decl, const char* scope_name)
{
    auto shadowed = symbol_table.insert_or_shadow(decl->name(), decl);
    if (shadowed != nullptr)
    {
        auto name = decl->name().c_str(state.ast.symbols);
        state.logger
            .log(clauf::diagnostic_kind::error, "duplicate %s declaration '%s'", scope_name, name)
            .annotation(clauf::annotation_kind::secondary, state.ast.location_of(shadowed),
                        "first declaration")
            .annotation(clauf::annotation_kind::primary, state.ast.location_of(decl),
                        "second declaration")
            .finish();
    }
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

constexpr auto identifier
    = dsl::identifier(dsl::unicode::xid_start_underscore, dsl::unicode::xid_continue);

constexpr auto kw_return = LEXY_KEYWORD("return", identifier);

constexpr auto kw_builtin_types
    = lexy::symbol_table<clauf::builtin_type::type_kind_t>.map(LEXY_LIT("int"),
                                                               clauf::builtin_type::int_);
constexpr auto kw_builtin_stmts = lexy::symbol_table<clauf::builtin_stmt::builtin_t> //
                                      .map(LEXY_LIT("__clauf_print"), clauf::builtin_stmt::print)
                                      .map(LEXY_LIT("__clauf_assert"), clauf::builtin_stmt::assert);

struct name
{
    static constexpr auto rule  = identifier.reserve(kw_return, dsl::literal_set(kw_builtin_types),
                                                     dsl::literal_set(kw_builtin_stmts));
    static constexpr auto value = callback<clauf::name>([](compiler_state& state, auto lexeme) {
        auto symbol = state.ast.symbols.intern(lexeme.data(), lexeme.size());
        return clauf::name{{lexeme.begin(), lexeme.end()}, symbol};
    });
};

} // namespace clauf::grammar

//=== type parsing ===//
namespace clauf::grammar
{
struct builtin_type
{
    static constexpr auto rule  = dsl::position(dsl::symbol<kw_builtin_types>);
    static constexpr auto value = construct<clauf::builtin_type>;
};

using type_specifier = builtin_type;
} // namespace clauf::grammar

//=== expression parsing ===//
namespace clauf::grammar
{
struct integer_constant_expr
{
    template <typename Base>
    static constexpr auto integer
        = dsl::integer<std::uint64_t>(dsl::digits<Base>.sep(dsl::digit_sep_tick));

    static constexpr auto rule = [] {
        auto decimal_digits = integer<dsl::decimal>;
        auto octal_digits   = integer<dsl::octal>;
        auto hex_digits     = (LEXY_LIT("0x") | LEXY_LIT("0X")) >> integer<dsl::hex>;
        auto binary_digits  = (LEXY_LIT("0b") | LEXY_LIT("0B")) >> integer<dsl::binary>;

        return dsl::peek(dsl::lit_c<'0'>)
                   >> dsl::position + (hex_digits | binary_digits | octal_digits)
               | dsl::else_ >> dsl::position(decimal_digits);
    }();

    static constexpr auto value = callback<clauf::integer_constant_expr*>(
        [](compiler_state& state, clauf::location loc, std::uint64_t value) {
            auto type = state.ast.create<clauf::builtin_type>({}, clauf::builtin_type::int_);
            return state.ast.create<clauf::integer_constant_expr>(loc, type, value);
        });
};

struct identifier_expr
{
    static constexpr auto rule = dsl::p<name>;

    static constexpr auto value
        = callback<clauf::identifier_expr*>([](compiler_state& state, clauf::name name) {
              auto decl = state.local_symbols.lookup(name.symbol);
              if (decl == nullptr)
                  decl = state.global_symbols.lookup(name.symbol);

              if (decl == nullptr)
              {
                  auto str = name.symbol.c_str(state.ast.symbols);
                  state.logger.log(diagnostic_kind::error, "unknown identifier '%s'", str)
                      .annotation(annotation_kind::primary, name.loc, "used here")
                      .finish();
              }

              auto type = clone_type(state, decl->type());
              return state.ast.create<clauf::identifier_expr>(name.loc, type, decl);
          });
};

template <typename Enum>
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

template <auto Enum, typename Rule>
constexpr auto op_(Rule rule)
{
    return dsl::op<op_tag_for<Enum>>(rule);
}

struct expr;
struct assignment_expr;

struct argument_list
{
    static constexpr auto rule = dsl::terminator(LEXY_LIT(")"))
                                     .opt_list(dsl::recurse<assignment_expr>, dsl::sep(dsl::comma));
    static constexpr auto value = lexy::as_list<clauf::expr_list>;
};

struct assignment_expr : lexy::expression_production
{
    static constexpr auto atom
        = dsl::parenthesized(dsl::recurse<expr>)
          | dsl::p<identifier_expr> | dsl::else_ >> dsl::p<integer_constant_expr>;

    struct postfix : dsl::postfix_op
    {
        static constexpr auto op = op_<0>(LEXY_LIT("(") >> dsl::p<argument_list>);
        using operand            = dsl::atom;
    };

    struct unary : dsl::prefix_op
    {
        static constexpr auto op = op_<clauf::unary_op::plus>(LEXY_LIT("+"))
                                   / op_<clauf::unary_op::neg>(LEXY_LIT("-"))
                                   / op_<clauf::unary_op::bnot>(LEXY_LIT("~"))
                                   / op_<clauf::unary_op::lnot>(LEXY_LIT("!"));
        using operand = postfix;
    };

    struct multiplicative : dsl::infix_op_left
    {
        static constexpr auto op = op_<clauf::arithmetic_op::mul>(LEXY_LIT("*"))
                                   / op_<clauf::arithmetic_op::div>(LEXY_LIT("/"))
                                   / op_<clauf::arithmetic_op::rem>(LEXY_LIT("%"));
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

    using operation = assignment;

    static constexpr auto value = callback<clauf::expr*>( //
        [](const compiler_state&, clauf::expr* expr) { return expr; },
        [](compiler_state& state, clauf::expr* fn, op_tag<int> op, clauf::expr_list arguments) {
            if (auto fn_type = dryad::node_try_cast<clauf::function_type>(fn->type()))
            {
                auto param_count
                    = std::distance(fn_type->parameters().begin(), fn_type->parameters().end());
                auto argument_count = std::distance(arguments.begin(), arguments.end());
                if (param_count != argument_count)
                {
                    state.logger
                        .log(clauf::diagnostic_kind::error,
                             "invalid argument count %zu for function with %zu parameter(s)",
                             argument_count, param_count)
                        .annotation(clauf::annotation_kind::primary, state.ast.location_of(fn),
                                    "call here")
                        .finish();
                }
            }
            else
            {
                state.logger
                    .log(clauf::diagnostic_kind::error, "called expression is not a function")
                    .annotation(clauf::annotation_kind::primary, state.ast.location_of(fn),
                                "call here")
                    .finish();
            }

            auto type = state.ast.create<clauf::builtin_type>({}, clauf::builtin_type::int_);
            return state.ast.create<clauf::function_call_expr>(op.loc, type, fn, arguments);
        },
        [](compiler_state& state, op_tag<clauf::unary_op> op, clauf::expr* child) {
            auto type = state.ast.create<clauf::builtin_type>({}, clauf::builtin_type::int_);
            return state.ast.create<clauf::unary_expr>(op.loc, type, op, child);
        },
        [](compiler_state& state, clauf::expr* left, op_tag<clauf::arithmetic_op> op,
           clauf::expr* right) {
            auto type = state.ast.create<clauf::builtin_type>({}, clauf::builtin_type::int_);
            return state.ast.create<clauf::arithmetic_expr>(op.loc, type, op, left, right);
        },
        [](compiler_state& state, clauf::expr* left, op_tag<clauf::comparison_op> op,
           clauf::expr* right) {
            auto type = state.ast.create<clauf::builtin_type>({}, clauf::builtin_type::int_);
            return state.ast.create<clauf::comparison_expr>(op.loc, type, op, left, right);
        },
        [](compiler_state& state, clauf::expr* left, op_tag<clauf::sequenced_op> op,
           clauf::expr* right) {
            auto type = state.ast.create<clauf::builtin_type>({}, clauf::builtin_type::int_);
            return state.ast.create<clauf::sequenced_expr>(op.loc, type, op, left, right);
        },
        [](compiler_state& state, clauf::expr* left, op_tag<clauf::assignment_op> op,
           clauf::expr* right) {
            // TODO: assert that left is an lvalue
            auto type = state.ast.create<clauf::builtin_type>({}, clauf::builtin_type::int_);
            return state.ast.create<clauf::assignment_expr>(op.loc, type, op, left, right);
        },
        [](compiler_state& state, clauf::expr* condition, op_tag<int> op, clauf::expr* if_true,
           clauf::expr* if_false) {
            auto type = state.ast.create<clauf::builtin_type>({}, clauf::builtin_type::int_);
            return state.ast.create<clauf::conditional_expr>(op.loc, type, condition, if_true,
                                                             if_false);
        });
};

struct expr : lexy::expression_production
{
    static constexpr auto atom = dsl::p<assignment_expr>;

    struct operation : dsl::infix_op_left
    {
        static constexpr auto op = op_<sequenced_op::comma>(dsl::comma);
        using operand            = dsl::atom;
    };

    static constexpr auto value = callback<clauf::expr*>( //
        [](const compiler_state&, clauf::expr* expr) { return expr; },
        [](compiler_state& state, clauf::expr* left, op_tag<clauf::sequenced_op> op,
           clauf::expr* right) {
            auto type = state.ast.create<clauf::builtin_type>({}, clauf::builtin_type::int_);
            return state.ast.create<clauf::sequenced_expr>(op.loc, type, op, left, right);
        });
};
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
            {
                insert_new_decl(state, state.local_symbols, decl, "local");
            }
            return result;
        });
};

struct expr_stmt
{
    static constexpr auto rule  = dsl::position + dsl::p<expr> + dsl::semicolon;
    static constexpr auto value = construct<clauf::expr_stmt>;
};

struct builtin_stmt
{
    static constexpr auto rule
        = dsl::position(dsl::symbol<kw_builtin_stmts>) >> dsl::p<expr> + dsl::semicolon;
    static constexpr auto value = construct<clauf::builtin_stmt>;
};

struct return_stmt
{
    static constexpr auto rule  = dsl::position(kw_return) >> dsl::p<expr> + dsl::semicolon;
    static constexpr auto value = construct<clauf::return_stmt>;
};

struct block_stmt
{
    static constexpr auto rule = dsl::position(dsl::curly_bracketed.opt_list(dsl::recurse<stmt>));

    static constexpr auto value = lexy::as_list<stmt_list> >> construct<clauf::block_stmt>;
};

struct stmt
{
    static constexpr auto rule
        = dsl::p<block_stmt> | dsl::p<builtin_stmt> //
          | dsl::p<return_stmt> | dsl::p<decl_stmt> | dsl::else_ >> dsl::p<expr_stmt>;
    static constexpr auto value = lexy::forward<clauf::stmt*>;
};
} // namespace clauf::grammar

//=== declaration ===//
namespace clauf::grammar
{
struct declarator;

struct parameter_decl
{
    static constexpr auto rule  = dsl::p<type_specifier> + dsl::recurse<declarator>;
    static constexpr auto value = callback<clauf::parameter_decl*>(
        [](compiler_state& state, clauf::type* type, clauf::declarator* decl) {
            auto name = get_name(decl);
            return state.ast.create<clauf::parameter_decl>(name.loc, name.symbol, type);
        });
};

struct parameter_list
{
    static constexpr auto rule
        = dsl::terminator(LEXY_LIT(")")).opt_list(dsl::p<parameter_decl>, dsl::sep(dsl::comma));
    static constexpr auto value = lexy::as_list<clauf::parameter_list>;
};

struct declarator : lexy::expression_production
{
    static constexpr auto atom = dsl::p<name> | dsl::parenthesized(dsl::recurse<declarator>);

    struct function_declarator : dsl::postfix_op
    {
        static constexpr auto op
            = dsl::op<function_declarator>(LEXY_LIT("(") >> dsl::position + dsl::p<parameter_list>);
        using operand = dsl::atom;
    };

    using operation = function_declarator;

    static constexpr auto value = callback<clauf::declarator*>( //
        [](const compiler_state&, clauf::declarator* decl) { return decl; },
        [](compiler_state& state, clauf::name name) {
            return state.decl_tree.create<clauf::name_declarator>(name);
        },
        [](compiler_state& state, clauf::declarator* child, function_declarator,
           clauf::location loc, clauf::parameter_list params) {
            return state.decl_tree.create<clauf::function_declarator>(loc, child, params);
        });
};

struct declarator_list
{
    static constexpr auto rule  = dsl::list(dsl::p<declarator>, dsl::sep(dsl::comma));
    static constexpr auto value = lexy::as_list<clauf::declarator_list>;
};

struct declaration
{
    static constexpr auto rule = dsl::p<type_specifier> >> dsl::p<declarator_list> + dsl::semicolon;

    static constexpr auto value = callback<clauf::decl_list>([](compiler_state& state, clauf::type*,
                                                                clauf::declarator_list decls) {
        clauf::decl_list result;
        for (auto decl : decls)
        {
            // TODO: we only have int as type, so just create a new int every time.
            // TODO: verify and compute correct return type
            auto type = state.ast.create<clauf::builtin_type>({}, clauf::builtin_type::int_);

            dryad::visit_node_all(
                decl,
                [&](clauf::name_declarator* name) {
                    auto var = state.ast.create<clauf::variable_decl>(name->name.loc,
                                                                      name->name.symbol, type);
                    result.push_back(var);
                },
                [&](clauf::function_declarator* decl) {
                    clauf::type_list parameter_types;
                    for (auto param : decl->parameters)
                    {
                        // TODO: clone the type of param
                        (void)param;
                        auto type
                            = state.ast.create<clauf::builtin_type>({}, clauf::builtin_type::int_);
                        parameter_types.push_back(type);
                    }

                    auto name = get_name(decl);
                    auto fn_type
                        = state.ast.create<clauf::function_type>({}, type, parameter_types);
                    auto fn = state.ast.create<clauf::function_decl>(name.loc, name.symbol, fn_type,
                                                                     decl->parameters);
                    result.push_back(fn);
                });
        }
        return result;
    });
};

struct global_declaration : lexy::scan_production<clauf::decl_list>
{
    template <typename Context, typename Reader>
    static scan_result scan(lexy::rule_scanner<Context, Reader>& scanner, compiler_state& state)
    {
        auto type = scanner.parse(grammar::type_specifier{});
        if (!type)
            return lexy::scan_failed;

        auto decl_list = scanner.parse(grammar::declarator_list{});
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

            auto decl = dryad::node_cast<clauf::function_declarator>(decl_list.value().front());
            auto name = get_name(decl);

            auto existing_decl = state.global_symbols.lookup(name.symbol);
            auto fn_decl = existing_decl ? dryad::node_try_cast<clauf::function_decl>(existing_decl)
                                         : nullptr;
            if (fn_decl != nullptr)
            {
                // TODO: verify that definition matches declaration
            }
            else
            {
                // TODO: check the declarator to get return type.
                clauf::type_list parameter_types;
                for (auto param : decl->parameters)
                {
                    // TODO: clone the type of param
                    (void)param;
                    auto type
                        = state.ast.create<clauf::builtin_type>({}, clauf::builtin_type::int_);
                    parameter_types.push_back(type);
                }

                auto fn_type
                    = state.ast.create<clauf::function_type>({}, type.value(), parameter_types);
                fn_decl = state.ast.create<clauf::function_decl>(name.loc, name.symbol, fn_type,
                                                                 decl->parameters);
                insert_new_decl(state, state.global_symbols, fn_decl, "global");
            }

            state.local_symbols = {};
            for (auto param : fn_decl->parameters())
                insert_new_decl(state, state.local_symbols, param, "local");

            auto body = scanner.parse(grammar::block_stmt{});
            if (!body)
                return lexy::scan_failed;
            fn_decl->set_body(body.value());

            return fn_decl->is_linked_in_tree() ? nullptr : fn_decl;
        }
        else
        {
            // We're having a declaration that isn't a function definition.
            scanner.parse(dsl::semicolon);
            if (!scanner)
                return lexy::scan_failed;

            auto result = grammar::declaration::value[state](type.value(), decl_list.value());
            for (auto decl : result)
                insert_new_decl(state, state.global_symbols, decl, "global");
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

