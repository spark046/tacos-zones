# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.28

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/spark046/Documents/Git/tacos-zones

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/spark046/Documents/Git/tacos-zones

# Include any dependencies generated for this target.
include test/CMakeFiles/test_heuristics.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include test/CMakeFiles/test_heuristics.dir/compiler_depend.make

# Include the progress variables for this target.
include test/CMakeFiles/test_heuristics.dir/progress.make

# Include the compile flags for this target's objects.
include test/CMakeFiles/test_heuristics.dir/flags.make

test/CMakeFiles/test_heuristics.dir/test_heuristics.cpp.o: test/CMakeFiles/test_heuristics.dir/flags.make
test/CMakeFiles/test_heuristics.dir/test_heuristics.cpp.o: test/test_heuristics.cpp
test/CMakeFiles/test_heuristics.dir/test_heuristics.cpp.o: test/CMakeFiles/test_heuristics.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --progress-dir=/home/spark046/Documents/Git/tacos-zones/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object test/CMakeFiles/test_heuristics.dir/test_heuristics.cpp.o"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT test/CMakeFiles/test_heuristics.dir/test_heuristics.cpp.o -MF CMakeFiles/test_heuristics.dir/test_heuristics.cpp.o.d -o CMakeFiles/test_heuristics.dir/test_heuristics.cpp.o -c /home/spark046/Documents/Git/tacos-zones/test/test_heuristics.cpp

test/CMakeFiles/test_heuristics.dir/test_heuristics.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Preprocessing CXX source to CMakeFiles/test_heuristics.dir/test_heuristics.cpp.i"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/spark046/Documents/Git/tacos-zones/test/test_heuristics.cpp > CMakeFiles/test_heuristics.dir/test_heuristics.cpp.i

test/CMakeFiles/test_heuristics.dir/test_heuristics.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Compiling CXX source to assembly CMakeFiles/test_heuristics.dir/test_heuristics.cpp.s"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/spark046/Documents/Git/tacos-zones/test/test_heuristics.cpp -o CMakeFiles/test_heuristics.dir/test_heuristics.cpp.s

# Object files for target test_heuristics
test_heuristics_OBJECTS = \
"CMakeFiles/test_heuristics.dir/test_heuristics.cpp.o"

# External object files for target test_heuristics
test_heuristics_EXTERNAL_OBJECTS =

test/test_heuristics: test/CMakeFiles/test_heuristics.dir/test_heuristics.cpp.o
test/test_heuristics: test/CMakeFiles/test_heuristics.dir/build.make
test/test_heuristics: src/search/libsearch.so
test/test_heuristics: _deps/catch2-build/src/libCatch2Maind.a
test/test_heuristics: /usr/lib64/libspdlog.so.1.12.0
test/test_heuristics: src/mtl_ata_translation/libmtl_ata_translation.so
test/test_heuristics: src/automata/libautomata.so
test/test_heuristics: /usr/lib64/libfmt.so.10.2.1
test/test_heuristics: _deps/catch2-build/src/libCatch2d.a
test/test_heuristics: test/CMakeFiles/test_heuristics.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --bold --progress-dir=/home/spark046/Documents/Git/tacos-zones/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable test_heuristics"
	cd /home/spark046/Documents/Git/tacos-zones/test && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/test_heuristics.dir/link.txt --verbose=$(VERBOSE)
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/cmake -D TEST_TARGET=test_heuristics -D TEST_EXECUTABLE=/home/spark046/Documents/Git/tacos-zones/test/test_heuristics -D TEST_EXECUTOR= -D TEST_WORKING_DIR=/home/spark046/Documents/Git/tacos-zones/test -D TEST_SPEC= -D TEST_EXTRA_ARGS= -D TEST_PROPERTIES= -D TEST_PREFIX= -D TEST_SUFFIX= -D TEST_LIST=test_heuristics_TESTS -D TEST_REPORTER= -D TEST_OUTPUT_DIR= -D TEST_OUTPUT_PREFIX= -D TEST_OUTPUT_SUFFIX= -D TEST_DL_PATHS= -D CTEST_FILE=/home/spark046/Documents/Git/tacos-zones/test/test_heuristics_tests-b12d07c.cmake -P /home/spark046/Documents/Git/tacos-zones/_deps/catch2-src/extras/CatchAddTests.cmake

# Rule to build all files generated by this target.
test/CMakeFiles/test_heuristics.dir/build: test/test_heuristics
.PHONY : test/CMakeFiles/test_heuristics.dir/build

test/CMakeFiles/test_heuristics.dir/clean:
	cd /home/spark046/Documents/Git/tacos-zones/test && $(CMAKE_COMMAND) -P CMakeFiles/test_heuristics.dir/cmake_clean.cmake
.PHONY : test/CMakeFiles/test_heuristics.dir/clean

test/CMakeFiles/test_heuristics.dir/depend:
	cd /home/spark046/Documents/Git/tacos-zones && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/spark046/Documents/Git/tacos-zones /home/spark046/Documents/Git/tacos-zones/test /home/spark046/Documents/Git/tacos-zones /home/spark046/Documents/Git/tacos-zones/test /home/spark046/Documents/Git/tacos-zones/test/CMakeFiles/test_heuristics.dir/DependInfo.cmake "--color=$(COLOR)"
.PHONY : test/CMakeFiles/test_heuristics.dir/depend

