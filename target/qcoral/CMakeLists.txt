# qcoral translator
add_executable(stg2qc QCoralTranslate.cpp QCoralPrinter.cpp)

target_include_directories(stg2qc PRIVATE ${CMAKE_SOURCE_DIR}/include)

target_link_libraries(stg2qc stg)
