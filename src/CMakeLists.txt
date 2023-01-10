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

FetchContent_Declare(lexy URL https://github.com/foonathan/lexy/releases/download/v2022.12.1/lexy-src.zip)
FetchContent_MakeAvailable(lexy)

FetchContent_Declare(lauf URL https://github.com/foonathan/lauf/archive/d90755684f8dfdf4364796eb6c2508f817a9ab98.zip)
FetchContent_MakeAvailable(lauf)

FetchContent_Declare(dryad URL https://github.com/foonathan/dryad/archive/82ff852be2edb072ade01643347177fd472dfb97.zip)
FetchContent_MakeAvailable(dryad)

file(DOWNLOAD
        https://github.com/CLIUtils/CLI11/releases/download/v2.2.0/CLI11.hpp
        ${CMAKE_CURRENT_BINARY_DIR}/CLI11.hpp)

find_package(PkgConfig REQUIRED)
pkg_check_modules(libffi REQUIRED IMPORTED_TARGET libffi)

#=== main executable ===#
add_executable(clauf)
target_sources(clauf PRIVATE ${source_files})
target_compile_features(clauf PRIVATE cxx_std_17)
target_include_directories(clauf PRIVATE ../include)
target_include_directories(clauf SYSTEM PRIVATE ${CMAKE_CURRENT_BINARY_DIR})
target_link_libraries(clauf PRIVATE foonathan::lexy foonathan::lauf foonathan::dryad PkgConfig::libffi ${CMAKE_DL_LIBS})

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

