// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <clauf/compiler.hpp>

#include <string>
#include <vector>

#include <dryad/symbol_table.hpp>
#include <lexy/action/parse.hpp>
#include <lexy/callback.hpp>
#include <lexy/dsl.hpp>
#include <lexy_ext/report_error.hpp>

#include <clauf/assert.hpp>
#include <clauf/ast.hpp>

//=== declarator tree ===//
namespace clauf
{
enum class declarator_kind
{
    name,
    function,
};

using declarator = dryad::node<declarator_kind>;

struct name_declarator : dryad::basic_node<declarator_kind::name>
{
    ast_symbol name;

    explicit name_declarator(dryad::node_ctor ctor, ast_symbol name) : node_base(ctor), name(name)
    {}
};

struct function_declarator
: dryad::basic_node<declarator_kind::function, dryad::container_node<declarator>>
{
    explicit function_declarator(dryad::node_ctor ctor, declarator* child) : node_base(ctor)
    {
        insert_child_after(nullptr, child);
    }

    DRYAD_CHILD_NODE_GETTER(declarator, child, nullptr)
};
} // namespace clauf

namespace
{
struct compiler_state
{
    mutable lexy_ext::diagnostic_writer<lexy::buffer<lexy::utf8_encoding>> diag;
    mutable clauf::ast                                                     ast;
    mutable dryad::tree<clauf::declarator_kind>                            decl_tree;
    mutable dryad::symbol_table<clauf::ast_symbol, clauf::decl*>           local_symbols;
    mutable bool                                                           errored = false;

    compiler_state(const lexy::buffer<lexy::utf8_encoding>& input)
    : diag(input, {lexy::visualize_fancy})
    {}
};

template <typename ReturnType, typename... Callback>
constexpr auto callback(Callback... cb)
{
    return lexy::bind(lexy::callback<ReturnType>(cb...), lexy::parse_state, lexy::values);
}
} // namespace

namespace clauf::grammar
{
namespace dsl = lexy::dsl;

constexpr auto identifier
    = dsl::identifier(dsl::unicode::xid_start_underscore, dsl::unicode::xid_continue);

constexpr auto kw_builtin_types
    = lexy::symbol_table<clauf::builtin_type::type_kind_t>.map(LEXY_LIT("int"),
                                                               clauf::builtin_type::int_);
constexpr auto kw_builtin_stmts = lexy::symbol_table<clauf::builtin_stmt::builtin_t> //
                                      .map(LEXY_LIT("__clauf_print"), clauf::builtin_stmt::print)
                                      .map(LEXY_LIT("__clauf_assert"), clauf::builtin_stmt::assert);
} // namespace clauf::grammar

//=== type parsing ===//
namespace clauf::grammar
{
struct builtin_type
{
    static constexpr auto rule  = dsl::symbol<kw_builtin_types>;
    static constexpr auto value = callback<clauf::builtin_type*>(
        [](const compiler_state& state, clauf::builtin_type::type_kind_t kind) {
            return state.ast.create<clauf::builtin_type>(kind);
        });
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

        return dsl::peek(dsl::lit_c<'0'>) >> (hex_digits | binary_digits | octal_digits)
               | dsl::else_ >> decimal_digits;
    }();

    static constexpr auto value = callback<clauf::integer_constant_expr*>(
        [](const compiler_state& state, std::uint64_t value) {
            auto type = state.ast.create<clauf::builtin_type>(clauf::builtin_type::int_);
            return state.ast.create<clauf::integer_constant_expr>(type, value);
        });
};

struct expr : lexy::expression_production
{
    static constexpr auto atom
        = dsl::parenthesized(dsl::recurse<expr>) | dsl::else_ >> dsl::p<integer_constant_expr>;

    struct unary : dsl::prefix_op
    {
        static constexpr auto op = dsl::op<clauf::unary_expr::plus>(LEXY_LIT("+"))
                                   / dsl::op<clauf::unary_expr::neg>(LEXY_LIT("-"))
                                   / dsl::op<clauf::unary_expr::bnot>(LEXY_LIT("~"))
                                   / dsl::op<clauf::unary_expr::lnot>(LEXY_LIT("!"));
        using operand = dsl::atom;
    };

    struct multiplicative : dsl::infix_op_left
    {
        static constexpr auto op = dsl::op<clauf::binary_expr::mul>(LEXY_LIT("*"))
                                   / dsl::op<clauf::binary_expr::div>(LEXY_LIT("/"))
                                   / dsl::op<clauf::binary_expr::rem>(LEXY_LIT("%"));
        using operand = unary;
    };

    struct additive : dsl::infix_op_left
    {
        static constexpr auto op = dsl::op<clauf::binary_expr::add>(LEXY_LIT("+"))
                                   / dsl::op<clauf::binary_expr::sub>(LEXY_LIT("-"));
        using operand = multiplicative;
    };

    struct shift : dsl::infix_op_left
    {
        static constexpr auto op = dsl::op<clauf::binary_expr::shl>(LEXY_LIT("<<"))
                                   / dsl::op<clauf::binary_expr::shr>(LEXY_LIT(">>"));
        using operand = additive;
    };

    struct relational : dsl::infix_op_left
    {
        static constexpr auto op
            = dsl::op<clauf::binary_expr::lt>(dsl::not_followed_by(LEXY_LIT("<"), LEXY_LIT("<")))
              / dsl::op<clauf::binary_expr::le>(LEXY_LIT("<="))
              / dsl::op<clauf::binary_expr::gt>(dsl::not_followed_by(LEXY_LIT(">"), LEXY_LIT(">")))
              / dsl::op<clauf::binary_expr::ge>(LEXY_LIT(">="));
        using operand = shift;
    };

    struct equality : dsl::infix_op_left
    {
        static constexpr auto op = dsl::op<clauf::binary_expr::eq>(LEXY_LIT("=="))
                                   / dsl::op<clauf::binary_expr::ne>(LEXY_LIT("!="));
        using operand = relational;
    };

    struct band : dsl::infix_op_left
    {
        static constexpr auto op = dsl::op<clauf::binary_expr::band>(LEXY_LIT("&"));
        using operand            = equality;
    };
    struct bxor : dsl::infix_op_left
    {
        static constexpr auto op = dsl::op<clauf::binary_expr::bxor>(LEXY_LIT("^"));
        using operand            = band;
    };
    struct bor : dsl::infix_op_left
    {
        static constexpr auto op = dsl::op<clauf::binary_expr::bor>(LEXY_LIT("|"));
        using operand            = bxor;
    };

    struct land : dsl::infix_op_left
    {
        static constexpr auto op = dsl::op<clauf::sequenced_binary_expr::land>(LEXY_LIT("&&"));
        using operand            = bor;
    };
    struct lor : dsl::infix_op_left
    {
        static constexpr auto op = dsl::op<clauf::sequenced_binary_expr::lor>(LEXY_LIT("||"));
        using operand            = land;
    };

    struct conditional : dsl::infix_op_right
    {
        static constexpr auto op
            = dsl::op<void>(LEXY_LIT("?") >> dsl::recurse<expr> + LEXY_LIT(":"));
        using operand = lor;
    };

    struct comma : dsl::infix_op_right
    {
        static constexpr auto op = dsl::op<clauf::sequenced_binary_expr::comma>(LEXY_LIT(","));
        using operand            = conditional;
    };

    using operation = comma;

    static constexpr auto value = callback<clauf::expr*>( //
        [](const compiler_state&, clauf::expr* expr) { return expr; },
        [](const compiler_state& state, clauf::unary_expr::op_t op, clauf::expr* child) {
            auto type = state.ast.create<clauf::builtin_type>(clauf::builtin_type::int_);
            return state.ast.create<clauf::unary_expr>(type, op, child);
        },
        [](const compiler_state& state, clauf::expr* left, clauf::binary_expr::op_t op,
           clauf::expr* right) {
            auto type = state.ast.create<clauf::builtin_type>(clauf::builtin_type::int_);
            return state.ast.create<clauf::binary_expr>(type, op, left, right);
        },
        [](const compiler_state& state, clauf::expr* left, clauf::sequenced_binary_expr::op_t op,
           clauf::expr* right) {
            auto type = state.ast.create<clauf::builtin_type>(clauf::builtin_type::int_);
            return state.ast.create<clauf::sequenced_binary_expr>(type, op, left, right);
        },
        [](const compiler_state& state, clauf::expr* condition, clauf::expr* if_true,
           clauf::expr* if_false) {
            auto type = state.ast.create<clauf::builtin_type>(clauf::builtin_type::int_);
            return state.ast.create<clauf::conditional_expr>(type, condition, if_true, if_false);
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
    static constexpr auto rule  = dsl::recurse_branch<declaration>;
    static constexpr auto value = callback<clauf::decl_stmt*>(
        [](const compiler_state& state, std::vector<clauf::decl*>&& decls) {
            auto result = state.ast.create<clauf::decl_stmt>();
            for (auto decl : decls)
            {
                result->add_declaration(decl);

                auto shadowed = state.local_symbols.insert_or_shadow(decl->name(), decl);
                if (shadowed != nullptr)
                {
                    auto out = lexy::cfile_output_iterator{stderr};
                    state.diag.write_message(out, lexy_ext::diagnostic_kind::error,
                                             [&](auto, lexy::visualization_options) {
                                                 auto name = decl->name().c_str(state.ast.symbols);
                                                 std::fprintf(stderr,
                                                              "duplicate local declaration '%s'",
                                                              name);
                                                 return out;
                                             });
                    state.errored = true;
                }
            }
            return result;
        });
};

struct expr_stmt
{
    static constexpr auto rule = dsl::p<expr> + dsl::semicolon;
    static constexpr auto value
        = callback<clauf::expr_stmt*>([](const compiler_state& state, clauf::expr* expr) {
              return state.ast.create<clauf::expr_stmt>(expr);
          });
};

struct builtin_stmt
{
    static constexpr auto rule  = dsl::symbol<kw_builtin_stmts> >> dsl::p<expr> + dsl::semicolon;
    static constexpr auto value = callback<clauf::builtin_stmt*>(
        [](const compiler_state& state, clauf::builtin_stmt::builtin_t builtin, clauf::expr* expr) {
            return state.ast.create<clauf::builtin_stmt>(builtin, expr);
        });
};

struct block_stmt
{
    static constexpr auto rule = dsl::curly_bracketed.opt_list(dsl::recurse<stmt>);

    static constexpr auto value
        = lexy::as_list<std::vector<clauf::stmt*>> >> callback<clauf::block_stmt*>(
              [](const compiler_state& state, lexy::nullopt) {
                  return state.ast.create<clauf::block_stmt>();
              },
              [](const compiler_state& state, auto&& stmts) {
                  auto result = state.ast.create<clauf::block_stmt>();
                  for (auto i = 0u; i < stmts.size(); ++i)
                      result->add_stmt_after(i == 0 ? nullptr : stmts[i - 1], stmts[i]);
                  return result;
              });
};

struct stmt
{
    static constexpr auto rule = dsl::p<block_stmt> | dsl::p<builtin_stmt> //
                                 | dsl::p<decl_stmt> | dsl::else_ >> dsl::p<expr_stmt>;
    static constexpr auto value = lexy::forward<clauf::stmt*>;
};
} // namespace clauf::grammar

//=== declaration ===//
namespace clauf::grammar
{
struct name
{
    static constexpr auto rule = identifier.reserve(dsl::literal_set(kw_builtin_types),
                                                    dsl::literal_set(kw_builtin_stmts));
    static constexpr auto value
        = callback<clauf::ast_symbol>([](const compiler_state& state, auto lexeme) {
              std::string str;
              for (auto c : lexeme)
                  str.push_back(c);
              return state.ast.symbols.intern(str.c_str(), lexeme.size());
          });
};

struct declarator : lexy::expression_production
{
    static constexpr auto atom = dsl::p<name> | dsl::parenthesized(dsl::recurse<declarator>);

    struct function_declarator : dsl::postfix_op
    {
        static constexpr auto op = dsl::op<function_declarator>(LEXY_LIT("(") >> LEXY_LIT(")"));
        using operand            = dsl::atom;
    };

    using operation = function_declarator;

    static constexpr auto value = callback<clauf::declarator*>( //
        [](const compiler_state&, clauf::declarator* decl) { return decl; },
        [](const compiler_state& state, clauf::ast_symbol name) {
            return state.decl_tree.create<clauf::name_declarator>(name);
        },
        [](const compiler_state& state, clauf::declarator* child, function_declarator) {
            return state.decl_tree.create<clauf::function_declarator>(child);
        });
};

struct declarator_list
{
    static constexpr auto rule  = dsl::list(dsl::p<declarator>, dsl::sep(dsl::comma));
    static constexpr auto value = lexy::as_list<std::vector<clauf::declarator*>>;
};

struct declaration
{
    static constexpr auto rule = dsl::p<type_specifier> >> dsl::p<declarator_list> + dsl::semicolon;

    [[maybe_unused]] static constexpr auto value = callback<std::vector<clauf::decl*>>(
        [](const compiler_state& state, clauf::type*, std::vector<clauf::declarator*>&& decls) {
            std::vector<clauf::decl*> result;
            for (auto decl : decls)
            {
                dryad::visit_node(
                    decl,
                    [&](clauf::name_declarator* name) {
                        // TODO: we only have int as type, so just create a new int every time.
                        auto type
                            = state.ast.create<clauf::builtin_type>(clauf::builtin_type::int_);
                        auto var = state.ast.create<clauf::variable_decl>(name->name, type);
                        result.push_back(var);
                    },
                    [](clauf::function_declarator* fn) {
                        if (auto name = dryad::node_try_cast<clauf::name_declarator>(fn->child()))
                        {
                            CLAUF_TODO("create function declaration");
                        }
                        else
                        {
                            CLAUF_TODO("generate error: function cannot return function");
                        }
                    });
            }
            return result;
        });
};

struct function_definition
{
    struct function_start
    {
        static constexpr auto rule = LEXY_LIT("");
        static constexpr auto value
            = callback<void>([](const compiler_state& state) { state.local_symbols = {}; });
    };

    static constexpr auto rule
        = dsl::p<type_specifier> + dsl::p<declarator> + dsl::p<function_start> + dsl::p<block_stmt>;

    static constexpr auto value
        = callback<clauf::function_decl*>([](const compiler_state& state, clauf::type* type,
                                             clauf::declarator* decl, clauf::block_stmt* body) {
              if (auto fn = dryad::node_try_cast<clauf::function_declarator>(decl))
              {
                  if (auto named = dryad::node_try_cast<clauf::name_declarator>(fn->child()))
                  {
                      auto fn_type = state.ast.create<clauf::function_type>(type);
                      return state.ast.create<clauf::function_decl>(named->name, fn_type, body);
                  }
              }

              CLAUF_TODO("generator error: not a function definition");
              return static_cast<clauf::function_decl*>(nullptr);
          });
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

    static constexpr auto rule = dsl::terminator(dsl::eof).list(dsl::p<function_definition>);
    static constexpr auto value
        = lexy::as_list<std::vector<clauf::decl*>> >> callback<void>(
              [](const compiler_state& state, const std::vector<clauf::decl*>& decls) {
                  auto tu = state.ast.create<clauf::translation_unit>();
                  for (auto d : decls)
                      tu->add_declaration(d);
                  state.ast.tree.set_root(tu);
              });
};
} // namespace clauf::grammar

std::optional<clauf::ast> clauf::compile(const lexy::buffer<lexy::utf8_encoding>& input)
{
    compiler_state state(input);
    auto           result
        = lexy::parse<clauf::grammar::translation_unit>(input, state, lexy_ext::report_error);
    if (!result || state.errored)
        return std::nullopt;

    return std::move(state.ast);
}

