add_executable(stgpp ConstraintDriver.cpp)

target_include_directories(stgpp PRIVATE ${CMAKE_SOURCE_DIR}/include)

target_link_libraries(stgpp stg)

