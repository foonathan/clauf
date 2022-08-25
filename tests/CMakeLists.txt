# Copyright (C) 2022 Jonathan Müller and clauf contributors
# SPDX-License-Identifier: BSL-1.0

file(GLOB test_files CONFIGURE_DEPENDS "integration/*.c")
foreach(file ${test_files})
    get_filename_component(name ${file} NAME)
    add_test(NAME ${name} COMMAND clauf ${file})
endforeach()

