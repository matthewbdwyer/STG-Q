# Unit tests need to access the development tree
include_directories(${CMAKE_SOURCE_DIR}/target/qcoral)
include_directories(${CMAKE_SOURCE_DIR}/target/fxp)

# The Catch2 framework and project specific helpers are used in unit tests
include_directories(${CMAKE_SOURCE_DIR}/lib/catch2)
include_directories(${CMAKE_SOURCE_DIR}/include)
include_directories(${CMAKE_SOURCE_DIR}/src/lib)
include_directories(${CMAKE_SOURCE_DIR}/src/tools)

add_subdirectory(qc)
add_subdirectory(fxp)