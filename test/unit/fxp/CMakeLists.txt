add_executable(fxp_unit_tests)

target_sources(fxp_unit_tests PUBLIC
        # First test defines CATCH_CONFIG_MAIN
        ${CMAKE_CURRENT_SOURCE_DIR}/fxpTest.cpp
        ${CMAKE_SOURCE_DIR}/target/fxp/FXPPrinter.cpp
)

target_link_libraries(fxp_unit_tests antlr4_static ${llvm_libs} stg coverage_config -ljsoncpp)