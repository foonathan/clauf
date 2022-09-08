# Copyright (C) 2022 Jonathan Müller and clauf contributors
# SPDX-License-Identifier: BSL-1.0

get_filename_component(include_dir ${CMAKE_CURRENT_SOURCE_DIR}/../include/clauf ABSOLUTE)
set(source_files
        ${include_dir}/assert.hpp
        ${include_dir}/ast.hpp
        ${include_dir}/codegen.hpp
        ${include_dir}/compiler.hpp
        ${include_dir}/diagnostic.hpp

        ast.cpp
        codegen.cpp
        compiler.cpp
        main.cpp)

#=== external dependencies ===#
include(FetchContent)

FetchContent_Declare(lexy URL https://lexy.foonathan.net/download/lexy-src.zip)
FetchContent_MakeAvailable(lexy)

FetchContent_Declare(lauf URL https://github.com/foonathan/lauf/archive/1971f26f864142094ef7cb9b1f6d4e4e86282752.zip)
FetchContent_MakeAvailable(lauf)

FetchContent_Declare(dryad URL https://github.com/foonathan/dryad/archive/607de8dd5ad142c303d797258ebd95f087c9524b.zip)
FetchContent_MakeAvailable(dryad)

file(DOWNLOAD 
        https://github.com/CLIUtils/CLI11/releases/download/v2.2.0/CLI11.hpp 
        ${CMAKE_CURRENT_BINARY_DIR}/CLI11.hpp)

#=== main executable ===#
add_executable(clauf)
target_sources(clauf PRIVATE ${source_files})
target_compile_features(clauf PRIVATE cxx_std_17)
target_include_directories(clauf PRIVATE ../include)
target_include_directories(clauf SYSTEM PRIVATE ${CMAKE_CURRENT_BINARY_DIR})
target_link_libraries(clauf PRIVATE foonathan::lexy foonathan::lauf foonathan::dryad)

if(${CMAKE_CXX_COMPILER_ID} STREQUAL "Clang")
    if("${CMAKE_CXX_SIMULATE_ID}" STREQUAL "MSVC")
        target_compile_options(clauf PRIVATE /WX /W3 /D _CRT_SECURE_NO_WARNINGS)
    else()
        target_compile_options(clauf PRIVATE -pedantic-errors -Werror -Wall -Wextra -Wconversion -Wsign-conversion)
    endif()
elseif(${CMAKE_CXX_COMPILER_ID} STREQUAL "GNU")
    target_compile_options(clauf PRIVATE -pedantic-errors -Werror -Wall -Wextra -Wconversion -Wsign-conversion)
elseif(MSVC)
    target_compile_options(clauf PRIVATE /WX /W3 /D _CRT_SECURE_NO_WARNINGS)
endif()

