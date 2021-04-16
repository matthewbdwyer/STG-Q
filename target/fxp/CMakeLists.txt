# fxp translator
add_executable(stg2fxp FXPTranslate.cpp FXPPrinter.cpp)

target_include_directories(stg2fxp PRIVATE ${CMAKE_SOURCE_DIR}/include)

target_link_libraries(stg2fxp stg -ljsoncpp)

install (TARGETS stg2fxp DESTINATION $ENV{STGQ_BIN})	

install(PROGRAMS Quantify.sh DESTINATION $ENV{STGQ_BIN})