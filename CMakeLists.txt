
project(STG-Q)

find_package(PkgConfig REQUIRED)

# minimum required CMAKE version
CMAKE_MINIMUM_REQUIRED(VERSION 3.15)

list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_SOURCE_DIR}/cmake)

# compiler must be 17
set(CMAKE_CXX_STANDARD 17)

# compile with debug flags
#`if(NOT CMAKE_BUILD_TYPE)
#` set(CMAKE_BUILD_TYPE Debug)
#`endif()

# Adding coverage
#add_compile_options(--coverage -O0)

#set(LDFLAGS "${LDFLAGS} --coverage")
#set(CXXFLAGS "${CXXFLAGS} --coverage")

######## ANTLR4 CPP target rules ###########

cmake_policy(PUSH)
# Allow the antlr jar to be found without execute permissions.
cmake_policy(SET CMP0109 OLD)
cmake_policy(SET CMP0114 NEW)

# required if linking to static library
add_definitions(-DANTLR4CPP_STATIC)

set(ANTLR4_WITH_STATIC_CRT OFF)
set(ANTLR4_TAG 4.9.2)
include(ExternalAntlr4Cpp)
include_directories(${ANTLR4_INCLUDE_DIRS})

# add macros to generate ANTLR Cpp code from grammar
find_package(ANTLR)
if(NOT ANTLR_FOUND)
  set(ANTLR_JAR antlr-${ANTLR4_TAG}-complete.jar)
  set(ANTLR_JAR_URL https://www.antlr.org/download/${ANTLR_JAR})
  message(STATUS "Downloading antlr jar into $ENV{STGQ_LIB}")
  file(DOWNLOAD ${ANTLR_JAR_URL} $ENV{STGQ_LIB}/${ANTLR_JAR})
  message(STATUS "Downloading complete")
  list(APPEND CMAKE_PROGRAM_PATH "$ENV{STGQ_LIB}")
  #  message(STATUS "${CMAKE_PROGRAM_PATH}")
  find_package(ANTLR REQUIRED)
endif()

cmake_policy(POP)

######## LLVM rules for installed libraries ###########
# We want to select the latest stable release even if others are installed

message(STATUS "system name: ${CMAKE_SYSTEM_NAME}")
if(CMAKE_SYSTEM_NAME STREQUAL "Linux")
  find_package(LLVM 11 REQUIRED CONFIG)
elseif(CMAKE_SYSTEM_NAME STREQUAL "Darwin")
  find_package(LLVM 11 REQUIRED CONFIG)
else()
  message(FATAL_ERROR "${CMAKE_SYSTEM_NAME} is not supported")
endif()

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

