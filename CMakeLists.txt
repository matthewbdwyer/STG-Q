
project(STG-Q)

# minimum required CMAKE version
CMAKE_MINIMUM_REQUIRED(VERSION 3.13)

list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_SOURCE_DIR}/cmake)

# compiler must be 17
set(CMAKE_CXX_STANDARD 17)

# compile with debug flags
#set(CMAKE_BUILD_TYPE Debug)

# Adding coverage
add_compile_options(--coverage -O0)

#set(LDFLAGS "${LDFLAGS} --coverage")
#set(CXXFLAGS "${CXXFLAGS} --coverage")

#CXXFLAGS = $(CXXFLAGS) ####### ANTLR4 CPP target rules ###########
# required if linking to static library
add_definitions(-DANTLR4CPP_STATIC)

# using /MD flag for antlr4_runtime (for Visual C++ compilers only)
set(ANTLR4_WITH_STATIC_CRT OFF)

# add external build for antlrcpp
include(ExternalAntlr4Cpp)

# add antrl4cpp artifacts to project environment
include_directories(${ANTLR4_INCLUDE_DIRS})

# set variable pointing to the antlr tool that supports C++
# this is not required if the jar file can be found under PATH environment
set(ANTLR_EXECUTABLE $ENV{STGQ_LIB}/antlr-4.8-complete.jar)

# add macros to generate ANTLR Cpp code from grammar
find_package(ANTLR REQUIRED)

######## LLVM rules ###########

# Executables use LLVM commandline parsing support
find_package(LLVM 11 REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

######## STG rules ###########

# STG constraint library
add_subdirectory(src)
include_directories(include)

# STG quantifier targets
add_subdirectory(target)

#add_subdirectory(test)
#target_link_libraries(stg2qc stg --coverage)

