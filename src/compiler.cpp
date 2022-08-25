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

template <typename ReturnType, typename Callback>
constexpr auto callback(Callback cb)
{
    return lexy::bind(lexy::callback<ReturnType>(cb), lexy::parse_state, lexy::values);
}
} // namespace

namespace clauf::grammar
{
namespace dsl = lexy::dsl;

constexpr auto identifier
    = dsl::identifier(dsl::unicode::xid_start_underscore, dsl::unicode::xid_continue);

constexpr auto kw_builtins
    = lexy::symbol_table<clauf::builtin_type::type_kind_t>.map(LEXY_LIT("int"),
                                                               clauf::builtin_type::int_);
} // namespace clauf::grammar

//=== type parsing ===//
namespace clauf::grammar
{
struct builtin_type
{
    static constexpr auto rule  = dsl::symbol<kw_builtins>;
    static constexpr auto value = callback<clauf::builtin_type*>(
        [](const compiler_state& state, clauf::builtin_type::type_kind_t kind) {
            return state.ast.create<clauf::builtin_type>(kind);
        });
};

using type = builtin_type;
} // namespace clauf::grammar

//=== declaration ===//
namespace clauf::grammar
{
struct name
{
    static constexpr auto rule = identifier.reserve(dsl::literal_set(kw_builtins));
    static constexpr auto value
        = callback<clauf::ast_symbol>([](const compiler_state& state, auto lexeme) {
              auto ptr = reinterpret_cast<const char*>(lexeme.data());
              return state.ast.symbols.intern(ptr, lexeme.size());
          });
};

struct function_decl
{
    static constexpr auto rule = dsl::p<type> + dsl::p<name> + LEXY_LIT("(") + LEXY_LIT(")")
                                 + LEXY_LIT("{") + LEXY_LIT("}");

    static constexpr auto value = callback<clauf::function_decl*>(
        [](const compiler_state& state, clauf::type* return_type, clauf::ast_symbol name) {
            auto fn_type = state.ast.create<clauf::function_type>(return_type);
            return state.ast.create<clauf::function_decl>(name, fn_type);
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

