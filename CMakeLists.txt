cmake_minimum_required(VERSION 3.24)
project(goto-lean VERSION 0.1.0 LANGUAGES C CXX)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin")
include(FetchContent)
set(GOTO_LEAN_CBMC_REV "32441ee38f8b2be63281a88a0df1a585dd4fdc43" CACHE STRING "CBMC commit")
set(FETCHCONTENT_UPDATES_DISCONNECTED ON)
set(enable_cbmc_tests OFF CACHE BOOL "" FORCE)
set(WITH_JBMC OFF CACHE BOOL "" FORCE)
set(WITH_MEMORY_ANALYZER OFF CACHE BOOL "" FORCE)
set(CMAKE_SKIP_INSTALL_RULES TRUE)
FetchContent_Declare(cbmc
  URL "https://github.com/diffblue/cbmc/archive/${GOTO_LEAN_CBMC_REV}.tar.gz"
  DOWNLOAD_EXTRACT_TIMESTAMP TRUE)
FetchContent_MakeAvailable(cbmc)
set_property(DIRECTORY "${cbmc_SOURCE_DIR}" PROPERTY EXCLUDE_FROM_ALL TRUE)
add_executable(goto-lean src/main.cpp src/printer.cpp)
# Reuse CBMC's value-layout code without linking its SAT solver backend.
target_sources(goto-lean PRIVATE "${cbmc_SOURCE_DIR}/src/solvers/flattening/boolbv_width.cpp")
target_link_libraries(goto-lean PRIVATE goto-programs)
target_compile_options(goto-lean PRIVATE -Wall -Wextra -Wpedantic -Wno-unused-parameter)
target_compile_definitions(goto-lean PRIVATE GOTO_LEAN_CBMC_REV="${GOTO_LEAN_CBMC_REV}")
add_custom_target(goto-lean-tools DEPENDS goto-lean goto-cc goto-instrument)
include(CTest)
if(BUILD_TESTING)
  add_executable(goto-lean-ir tests/ir.cpp)
  target_link_libraries(goto-lean-ir PRIVATE goto-programs)
  set_target_properties(goto-lean-ir PROPERTIES EXCLUDE_FROM_ALL TRUE)
  add_dependencies(goto-lean-tools goto-lean-ir)
  find_package(Python3 REQUIRED COMPONENTS Interpreter)
  find_program(LAKE_EXECUTABLE lake REQUIRED)
  find_program(MAKE_EXECUTABLE make REQUIRED)
  add_test(NAME goto-lean-tests COMMAND "${Python3_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/tests/run.py"
    --printer $<TARGET_FILE:goto-lean> --goto-cc $<TARGET_FILE:goto-cc>
    --ir $<TARGET_FILE:goto-lean-ir> --lake "${LAKE_EXECUTABLE}" --work "${CMAKE_BINARY_DIR}/tests")
  set_tests_properties(goto-lean-tests PROPERTIES TIMEOUT 300)
  add_test(NAME goto-lean-translate COMMAND "${Python3_EXECUTABLE}"
    "${CMAKE_SOURCE_DIR}/tests/translate.py" "${CMAKE_BINARY_DIR}")
  set_tests_properties(goto-lean-translate PROPERTIES
    TIMEOUT 180 RUN_SERIAL TRUE DEPENDS goto-lean-tests)
  add_test(NAME goto-lean-memory COMMAND "${Python3_EXECUTABLE}"
    "${CMAKE_SOURCE_DIR}/tests/memory.py" "${CMAKE_BINARY_DIR}")
  set_tests_properties(goto-lean-memory PROPERTIES TIMEOUT 300)
  add_test(NAME goto-lean-options COMMAND "${Python3_EXECUTABLE}"
    "${CMAKE_SOURCE_DIR}/tests/options.py" "${CMAKE_BINARY_DIR}")
  set_tests_properties(goto-lean-options PROPERTIES TIMEOUT 300 RUN_SERIAL TRUE)
  add_test(NAME goto-lean-calls COMMAND "${Python3_EXECUTABLE}"
    "${CMAKE_SOURCE_DIR}/tests/calls.py" "${CMAKE_BINARY_DIR}")
  set_tests_properties(goto-lean-calls PROPERTIES TIMEOUT 300)
  add_test(NAME goto-lean-provenance COMMAND "${CMAKE_COMMAND}" -E env
    "GOTO_CC=$<TARGET_FILE:goto-cc>" "GOTO_LEAN=$<TARGET_FILE:goto-lean>"
    "GOTO_INSTRUMENT=$<TARGET_FILE:goto-instrument>"
    "${Python3_EXECUTABLE}" "${CMAKE_SOURCE_DIR}/tests/verification.py")
  set_tests_properties(goto-lean-provenance PROPERTIES TIMEOUT 180 RUN_SERIAL TRUE)
  add_test(NAME goto-lean-parser COMMAND "${CMAKE_COMMAND}" -E env
    "GOTO_CC=$<TARGET_FILE:goto-cc>" "GOTO_LEAN=$<TARGET_FILE:goto-lean>"
    "${MAKE_EXECUTABLE}" check)
  set_tests_properties(goto-lean-parser PROPERTIES
    WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}/examples/parser" TIMEOUT 120 RUN_SERIAL TRUE)
  add_test(NAME goto-lean-checks COMMAND "${CMAKE_COMMAND}" -E env
    "GOTO_CC=$<TARGET_FILE:goto-cc>" "GOTO_LEAN=$<TARGET_FILE:goto-lean>"
    "GOTO_INSTRUMENT=$<TARGET_FILE:goto-instrument>"
    "${MAKE_EXECUTABLE}" check probe-pointer)
  set_tests_properties(goto-lean-checks PROPERTIES
    WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}/examples/checks" TIMEOUT 120 RUN_SERIAL TRUE)
  add_test(NAME goto-lean-violations COMMAND "${CMAKE_COMMAND}" -E env
    "GOTO_CC=$<TARGET_FILE:goto-cc>" "GOTO_LEAN=$<TARGET_FILE:goto-lean>"
    "GOTO_INSTRUMENT=$<TARGET_FILE:goto-instrument>"
    "${MAKE_EXECUTABLE}" check)
  set_tests_properties(goto-lean-violations PROPERTIES
    WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}/examples/violations" TIMEOUT 120 RUN_SERIAL TRUE)
  find_program(CBMC_EXECUTABLE cbmc)
  if(CBMC_EXECUTABLE)
    add_test(NAME goto-lean-violations-cbmc COMMAND "${CMAKE_COMMAND}" -E env
      "GOTO_CC=$<TARGET_FILE:goto-cc>" "GOTO_LEAN=$<TARGET_FILE:goto-lean>"
      "GOTO_INSTRUMENT=$<TARGET_FILE:goto-instrument>" "CBMC=${CBMC_EXECUTABLE}"
      "${MAKE_EXECUTABLE}" cbmc)
    set_tests_properties(goto-lean-violations-cbmc PROPERTIES
      WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}/examples/violations" TIMEOUT 120 RUN_SERIAL TRUE)
  endif()
  add_test(NAME goto-lean-arrays COMMAND "${CMAKE_COMMAND}" -E env
    "GOTO_CC=$<TARGET_FILE:goto-cc>" "GOTO_LEAN=$<TARGET_FILE:goto-lean>"
    "GOTO_INSTRUMENT=$<TARGET_FILE:goto-instrument>"
    "${MAKE_EXECUTABLE}" check checked)
  set_tests_properties(goto-lean-arrays PROPERTIES
    WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}/examples/arrays" TIMEOUT 120 RUN_SERIAL TRUE)
  add_test(NAME goto-lean-case-studies COMMAND "${CMAKE_COMMAND}" -E env
    "GOTO_CC=$<TARGET_FILE:goto-cc>" "GOTO_LEAN=$<TARGET_FILE:goto-lean>"
    "GOTO_INSTRUMENT=$<TARGET_FILE:goto-instrument>"
    "${MAKE_EXECUTABLE}" check)
  set_tests_properties(goto-lean-case-studies PROPERTIES
    WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}/examples/case-studies"
    TIMEOUT 180 RUN_SERIAL TRUE DEPENDS goto-lean-tests)
endif()
