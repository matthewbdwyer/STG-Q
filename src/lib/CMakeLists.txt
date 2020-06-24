######## Library specific rules ###########

# Call macro to add lexer and grammar to build dependencies
antlr_target(STG ConstraintGrammar.g4 VISITOR)

# STG constraint library
add_library(stg STATIC
            ConstraintBuilder.cpp
            ConstraintBuilder.h
            Constraint.cpp
            ConstraintPrinter.cpp
            ${ANTLR_STG_CXX_OUTPUTS})

# These includes are not required by the STG public include files
target_include_directories(stg PRIVATE
            ${ANTLR_STG_OUTPUT_DIR} 
            ${CMAKE_SOURCE_DIR}/include)

target_link_libraries(stg antlr4_static)

