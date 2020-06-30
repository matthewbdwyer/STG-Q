add_executable(stgpp stgpp.cpp ConstraintTypeChecker.cpp ConstraintFolder.cpp)

# Make the LLVM definitions visible so that we can include support
# for commandline parsing.
add_definitions(${LLVM_DEFINITIONS})

target_include_directories(stgpp PRIVATE 
                           ${LLVM_INCLUDE_DIRS} 
                           ${CMAKE_SOURCE_DIR}/include )

llvm_map_components_to_libnames(llvm_libs Support)

target_link_libraries(stgpp stg ${llvm_libs})

