// Copyright (C) 2022 Jonathan Müller and clauf contributors
// SPDX-License-Identifier: BSL-1.0

#ifndef CLAUF_ASSERT_HPP_INCLUDED
#define CLAUF_ASSERT_HPP_INCLUDED

#include <cassert>
#include <cstdio>

#define CLAUF_PRECONDITION(Condition) assert(Condition)
#define CLAUF_ASSERT(Condition, Msg) assert((Condition) && (Msg))
#define CLAUF_UNREACHABLE(Msg) assert(::clauf::_detail::unreachable(Msg))

#define CLAUF_TODO(Msg)                                                                            \
    (std::fprintf(stderr, "%s:%d: TODO: %s\n", __FILE__, __LINE__, (Msg)),                         \
     ::clauf::_detail::todo_reached = true)

#define CLAUF_UNIMPLEMENTED(Msg)                                                                   \
    (assert(::clauf::_detail::unimplemented(Msg)), ::clauf::_detail::unimplemented_value{})

namespace clauf::_detail
{
// Mutable global variable, I know.
inline bool todo_reached = false;

constexpr bool unreachable(const char*)
{
    return false;
}

constexpr bool unimplemented(const char*)
{
    return false;
}

// Convertible to anything using UB.
struct unimplemented_value
{
    template <typename T>
    operator T&() const
    {
        return *static_cast<T*>(nullptr);
    }
};
} // namespace clauf::_detail

#endif // CLAUF_ASSERT_HPP_INCLUDED

