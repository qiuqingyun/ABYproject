cmake_minimum_required(VERSION 3.12)
project(ABYTIME LANGUAGES CXX)

# Write built executables and libraries to bin/ and lib/, respectively.
if(NOT CMAKE_RUNTIME_OUTPUT_DIRECTORY)
    set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}/../bin")
endif()
if(NOT CMAKE_LIBRARY_OUTPUT_DIRECTORY)
    set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}/lib")
endif()
if(NOT CMAKE_ARCHIVE_OUTPUT_DIRECTORY)
    set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}/lib")
endif()

 find_package(ABY QUIET)
 if(ABY_FOUND)
 	message(STATUS "Found ABY")
 elseif (NOT ABY_FOUND AND NOT TARGET ABY::aby)
 	message("ABY was not found: add ABY subdirectory")
 	add_subdirectory(extern/ABY)
 endif()

add_subdirectory(src)
