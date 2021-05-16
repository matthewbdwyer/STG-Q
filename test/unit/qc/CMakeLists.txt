add_executable(qcoral_unit_tests)

target_sources(qcoral_unit_tests PUBLIC
        # First test defines CATCH_CONFIG_MAIN
        ${CMAKE_CURRENT_SOURCE_DIR}/qcoralTest.cpp
        ${CMAKE_SOURCE_DIR}/target/qcoral/QCoralPrinter.cpp
)

#target_include_directories(qcoral_unit_tests PUBLIC ${CMAKE_SOURCE_DIR}/target/qcoral)
#target_include_directories(qcoral_unit_tests PUBLIC ${CMAKE_SOURCE_DIR}/src/lib)
#target_include_directories(qcoral_unit_tests PUBLIC ${CMAKE_SOURCE_DIR}/src/tools)
#target_include_directories(qcoral_unit_tests PUBLIC ${CMAKE_SOURCE_DIR}/include)

target_link_libraries(qcoral_unit_tests antlr4_static ${llvm_libs} stg coverage_config)