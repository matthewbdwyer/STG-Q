add_executable(smt_unit_tests)

target_sources(smt_unit_tests PUBLIC
        # First test defines CATCH_CONFIG_MAIN
        ${CMAKE_CURRENT_SOURCE_DIR}/smtTest.cpp
        ${CMAKE_SOURCE_DIR}/target/smt/SMTPrinter.cpp
)

target_link_libraries(smt_unit_tests antlr4_static ${llvm_libs} stg coverage_config -ljsoncpp)