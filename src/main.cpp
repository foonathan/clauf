// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#include <CLI11.hpp>
#include <cstdio>
#include <lexy/input/file.hpp>
#include <string>

#include <lauf/asm/program.h>
#include <lauf/backend/dump.h>
#include <lauf/runtime/value.h>
#include <lauf/vm.h>
#include <lauf/writer.h>

#include <clauf/assert.hpp>
#include <clauf/ast.hpp>
#include <clauf/codegen.hpp>
#include <clauf/compiler.hpp>

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
    auto file = lexy::read_file<lexy::utf8_char_encoding>(opts.input.c_str());
    if (!file)
    {
        std::fprintf(stderr, "error: input file '%s' not found.\n", opts.input.c_str());
        return 1;
    }

    auto ast = compile(file.buffer());
    if (!ast)
        return 1;

    if (opts.dump_ast)
    {
        std::puts("=== AST ===");
        dump_ast(*ast);
        std::putchar('\n');
    }

    auto mod = codegen(*ast);
    if (opts.dump_bytecode)
    {
        std::puts("=== BYTECODE ===");
        auto writer = lauf_create_stdout_writer();
        lauf_backend_dump(writer, lauf_backend_default_dump_options, mod);
        lauf_destroy_writer(writer);
        std::putchar('\n');
    }

    auto exit_code = 0;
    if (!opts.compile_only)
    {
        auto vm = lauf_create_vm(lauf_default_vm_options);

        auto main_fn = lauf_asm_find_function_by_name(mod, "main");
        if (main_fn == nullptr)
        {
            std::fprintf(stderr, "Program does not contain main.\n");
            return 1;
        }
        if (auto sig = lauf_asm_function_signature(main_fn);
            sig.input_count != 0 || sig.output_count != 1)
        {
            std::fprintf(stderr, "main signature is wrong: (%d => %d)\n", sig.input_count,
                         sig.output_count);
            return 1;
        }

        auto program = lauf_asm_create_program(mod, main_fn);

        lauf_runtime_value return_code;
        if (!lauf_vm_execute_oneshot(vm, program, nullptr, &return_code))
            return 1;
        exit_code = static_cast<int>(return_code.as_sint);

        lauf_destroy_vm(vm);
    }

    // Exit code 70 is EX_SOFTWARE in sysexits.h
    return clauf::_detail::todo_reached ? 70 : exit_code;
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

