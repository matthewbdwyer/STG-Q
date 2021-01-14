# smt translator
add_executable(stg2smt SMTTranslate.cpp SMTPrinter.cpp)

target_include_directories(stg2smt PRIVATE ${CMAKE_SOURCE_DIR}/include)

target_link_libraries(stg2smt stg --coverage -ljsoncpp)
