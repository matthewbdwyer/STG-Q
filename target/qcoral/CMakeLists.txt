# qcoral translator
add_executable(stg2qc QCoralTranslate.cpp QCoralPrinter.cpp)
add_executable(comb QC_Combine.cpp)
add_executable(res QC_Result.cpp)

target_include_directories(stg2qc PRIVATE ${CMAKE_SOURCE_DIR}/include)

target_link_libraries(stg2qc stg)

install (TARGETS stg2qc DESTINATION $ENV{STGQ_BIN})
install (TARGETS comb DESTINATION $ENV{STGQ_BIN})
install (TARGETS res DESTINATION $ENV{STGQ_BIN})

install(PROGRAMS Quantify.sh DESTINATION $ENV{STGQ_BIN})
install(PROGRAMS QC_Quantify.sh DESTINATION $ENV{STGQ_BIN})

