# Copyright (C) 2022 Jonathan Müller and clauf contributors
# SPDX-License-Identifier: BSL-1.0

#=== external dependencies ===#
include(FetchContent)
FetchContent_Declare(lexy URL https://lexy.foonathan.net/download/lexy-src.zip)
FetchContent_MakeAvailable(lexy)

file(DOWNLOAD 
        https://github.com/CLIUtils/CLI11/releases/download/v2.2.0/CLI11.hpp 
        ${CMAKE_CURRENT_BINARY_DIR}/CLI11.hpp)

#=== main executable ===#
add_executable(clauf main.cpp)
target_compile_features(clauf PRIVATE cxx_std_17)
target_include_directories(clauf PRIVATE ../include ${CMAKE_CURRENT_BINARY_DIR})
target_link_libraries(clauf PRIVATE foonathan::lexy)

