# bv translator
add_executable(stg2bv BVTranslate.cpp BVPrinter.cpp)

target_include_directories(stg2bv PRIVATE ${CMAKE_SOURCE_DIR}/include)

target_link_libraries(stg2bv stg --coverage -ljsoncpp)
