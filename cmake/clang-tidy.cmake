set(CREATE_CLANG_TIDIABLE_SCRIPT
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake/create-clang-tidiable.sh"
    CACHE STRING "")

function(clang_tidy_header HEADER TARGET STANDARD)
    file(RELATIVE_PATH CT_NAME ${CMAKE_SOURCE_DIR} ${HEADER})
    string(REPLACE "/" "_" CT_NAME ${CT_NAME})
    get_filename_component(CT_NAME ${CT_NAME} NAME_WLE)
    set(CT_NAME "clang-tidy_${CT_NAME}")
    set(CPP_NAME
        "${CMAKE_BINARY_DIR}/generated-sources/${TARGET}/${CT_NAME}.cpp")

    add_custom_command(
        OUTPUT "${CPP_NAME}"
        COMMAND ${CMAKE_COMMAND} -E make_directory
                "${CMAKE_BINARY_DIR}/generated-sources/${TARGET}"
        COMMAND "${CREATE_CLANG_TIDIABLE_SCRIPT}" ${CPP_NAME} ${HEADER}
        DEPENDS ${HEADER} ${CMAKE_SOURCE_DIR}/.clang-tidy)

    add_library(${CT_NAME} EXCLUDE_FROM_ALL ${CPP_NAME})
    target_link_libraries(${CT_NAME} PRIVATE ${TARGET})
    target_compile_features(${CT_NAME} PRIVATE cxx_std_${STANDARD})
    set_target_properties(
        ${CT_NAME}
        PROPERTIES
            CXX_CLANG_TIDY
            "${CLANG_TIDY_PROGRAM};-p;${CMAKE_BINARY_DIR};-header-filter=${HEADER}"
    )

    add_dependencies(clang-tidy "${CT_NAME}")
endfunction()

function(clang_tidy_interface TARGET STANDARD)
    get_target_property(DIRS ${TARGET} INTERFACE_INCLUDE_DIRECTORIES)
    get_target_property(SYSTEM_DIRS ${TARGET}
                        INTERFACE_SYSTEM_INCLUDE_DIRECTORIES)
    foreach(DIR ${DIRS})
        if(NOT DIR IN_LIST SYSTEM_DIRS)
            file(GLOB_RECURSE HEADERS "${DIR}/*.hpp")
            foreach(HEADER ${HEADERS})
                clang_tidy_header(${HEADER} ${TARGET} ${STANDARD})
            endforeach()
        endif()
    endforeach()
endfunction()
