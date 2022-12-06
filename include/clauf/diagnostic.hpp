// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#ifndef CLAUF_DIAGNOSTIC_HPP_INCLUDED
#define CLAUF_DIAGNOSTIC_HPP_INCLUDED

#include <clauf/ast.hpp>
#include <lexy_ext/report_error.hpp>

namespace clauf
{
using lexy_ext::annotation_kind;
using lexy_ext::diagnostic_kind;

class diagnostic_logger
{
public:
    explicit diagnostic_logger(const file& file) : _file(&file), _errored(false) {}

    explicit operator bool() const
    {
        return !_errored;
    }

    class writer
    {
    public:
        [[gnu::format(printf, 4, 5), nodiscard]] writer& annotation(lexy_ext::annotation_kind kind,
                                                                    clauf::location           loc,
                                                                    const char* fmt, ...)
        {
            auto begin_loc = lexy::get_input_location(_file->buffer(), loc.begin);

            va_list args;
            va_start(args, fmt);
            _impl.write_empty_annotation(lexy::cfile_output_iterator{stderr});
            _impl.write_annotation(lexy::cfile_output_iterator{stderr}, kind, begin_loc, loc.end,
                                   [&](auto out, lexy::visualization_options) {
                                       std::vfprintf(stderr, fmt, args);
                                       return out;
                                   });
            va_end(args);
            return *this;
        }

        void finish() {}

    private:
        writer(const file* file) : _file(file), _impl(file->buffer(), {lexy::visualize_fancy}) {}

        const file*                                                         _file;
        lexy_ext::diagnostic_writer<lexy::buffer<lexy::utf8_char_encoding>> _impl;

        friend diagnostic_logger;
    };

    [[gnu::format(printf, 3, 4)]] writer log(lexy_ext::diagnostic_kind kind, const char* fmt, ...)
    {
        writer  result(_file);
        va_list args;
        va_start(args, fmt);

        result._impl.write_message(lexy::cfile_output_iterator{stderr}, kind,
                                   [&](auto out, lexy::visualization_options) {
                                       std::vfprintf(stderr, fmt, args);
                                       return out;
                                   });
        result._impl.write_path(lexy::cfile_output_iterator{stderr}, _file->path());

        va_end(args);
        if (kind == lexy_ext::diagnostic_kind::error)
            _errored = true;
        return result;
    }

    auto error_callback() const
    {
        return lexy_ext::report_error.opts({lexy::visualize_fancy}).path(_file->path());
    }

private:
    const file* _file;
    bool        _errored;
};
} // namespace clauf

#endif // CLAUF_DIAGNOSTIC_HPP_INCLUDED

