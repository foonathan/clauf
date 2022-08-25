// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <CLI11.hpp>
#include <cstdio>
#include <lauf/vm.h>
#include <lexy/input/file.hpp>
#include <string>

#include <clauf/assert.hpp>

namespace clauf
{
struct options
{
    std::string input;
    bool        compile_only  = false;
    bool        dump_ast      = false;
    bool        dump_bytecode = false;
};

int main(const options& opts)
{
    auto file = lexy::read_file<lexy::utf8_encoding>(opts.input.c_str());
    if (!file)
    {
        std::fprintf(stderr, "error: input file '%s' not found.\n", opts.input.c_str());
        return 1;
    }

    CLAUF_TODO("compile file");
    if (opts.dump_ast)
    {
        CLAUF_TODO("dump ast");
    }

    CLAUF_TODO("generate bytecode");
    if (opts.dump_bytecode)
    {
        CLAUF_TODO("dump bytecode");
    }

    if (!opts.compile_only)
    {
        auto vm = lauf_create_vm(lauf_default_vm_options);

        CLAUF_TODO("execute");

        lauf_destroy_vm(vm);
    }

    // Exit code 70 is EX_SOFTWARE in sysexits.h
    return clauf::_detail::todo_reached ? 70 : 0;
}
} // namespace clauf

int main(int argc, char* argv[])
{
    CLI::App       app("C interpreter");
    clauf::options options;

    app.add_option("input", options.input, "The C file to be interpreted.")->required();

    app.add_flag("--compile-only", options.compile_only, "Only compile, don't execute.");
    app.add_flag("--dump-ast", options.dump_ast, "Dump AST to stdout.");
    app.add_flag("--dump-bytecode", options.dump_bytecode, "Dump Bytecode to stdout.");

    CLI11_PARSE(app, argc, argv);

    return clauf::main(options);
}

