// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <clauf/compiler.hpp>

#include <vector>

#include <lexy/action/parse.hpp>
#include <lexy/callback.hpp>
#include <lexy/dsl.hpp>
#include <lexy_ext/report_error.hpp>

#include <clauf/assert.hpp>
#include <clauf/ast.hpp>

namespace
{
struct compiler_state
{
    mutable clauf::ast ast;
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

using type = builtin_type;
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
    static constexpr auto atom = dsl::p<integer_constant_expr>;

    struct multiplicative : dsl::infix_op_left
    {
        static constexpr auto op = dsl::op<clauf::binary_expr::mul>(LEXY_LIT("*"))
                                   / dsl::op<clauf::binary_expr::div>(LEXY_LIT("/"))
                                   / dsl::op<clauf::binary_expr::rem>(LEXY_LIT("%"));
        using operand = dsl::atom;
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
              / dsl::op<clauf::binary_expr::gt>(LEXY_LIT(">="));
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

    using operation = bor;

    static constexpr auto value = callback<clauf::expr*>( //
        [](const compiler_state&, clauf::integer_constant_expr* expr) { return expr; },
        [](const compiler_state& state, clauf::expr* left, clauf::binary_expr::op_t op,
           clauf::expr* right) {
            auto type = state.ast.create<clauf::builtin_type>(clauf::builtin_type::int_);
            return state.ast.create<clauf::binary_expr>(type, op, left, right);
        });
};
} // namespace clauf::grammar

//=== statement parsing ===//
namespace clauf::grammar
{
struct stmt;

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
    static constexpr auto rule
        = dsl::p<block_stmt> | dsl::p<builtin_stmt> | dsl::else_ >> dsl::p<expr_stmt>;
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
              auto ptr = reinterpret_cast<const char*>(lexeme.data());
              return state.ast.symbols.intern(ptr, lexeme.size());
          });
};

struct function_decl
{
    static constexpr auto rule
        = dsl::p<type> + dsl::p<name> + LEXY_LIT("(") + LEXY_LIT(")") + dsl::p<block_stmt>;

    static constexpr auto value
        = callback<clauf::function_decl*>([](const compiler_state& state, clauf::type* return_type,
                                             clauf::ast_symbol name, clauf::block_stmt* body) {
              auto fn_type = state.ast.create<clauf::function_type>(return_type);
              return state.ast.create<clauf::function_decl>(name, fn_type, body);
          });
};

using decl = function_decl;
} // namespace clauf::grammar

//=== translation unit ===//
namespace clauf::grammar
{
struct translation_unit
{
    static constexpr auto whitespace = dsl::ascii::space
                                       | LEXY_LIT("//") >> dsl::until(dsl::newline)
                                       | LEXY_LIT("/*") >> dsl::until(LEXY_LIT("*/"));

    static constexpr auto rule = dsl::terminator(dsl::eof).list(dsl::p<decl>);
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
    compiler_state state;
    auto           result
        = lexy::parse<clauf::grammar::translation_unit>(input, state, lexy_ext::report_error);
    if (!result)
        return std::nullopt;

    return std::move(state.ast);
}

