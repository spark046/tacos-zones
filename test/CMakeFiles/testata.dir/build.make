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
include test/CMakeFiles/testata.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include test/CMakeFiles/testata.dir/compiler_depend.make

# Include the progress variables for this target.
include test/CMakeFiles/testata.dir/progress.make

# Include the compile flags for this target's objects.
include test/CMakeFiles/testata.dir/flags.make

test/CMakeFiles/testata.dir/test_ata_formula.cpp.o: test/CMakeFiles/testata.dir/flags.make
test/CMakeFiles/testata.dir/test_ata_formula.cpp.o: test/test_ata_formula.cpp
test/CMakeFiles/testata.dir/test_ata_formula.cpp.o: test/CMakeFiles/testata.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --progress-dir=/home/spark046/Documents/Git/tacos-zones/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object test/CMakeFiles/testata.dir/test_ata_formula.cpp.o"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT test/CMakeFiles/testata.dir/test_ata_formula.cpp.o -MF CMakeFiles/testata.dir/test_ata_formula.cpp.o.d -o CMakeFiles/testata.dir/test_ata_formula.cpp.o -c /home/spark046/Documents/Git/tacos-zones/test/test_ata_formula.cpp

test/CMakeFiles/testata.dir/test_ata_formula.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Preprocessing CXX source to CMakeFiles/testata.dir/test_ata_formula.cpp.i"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/spark046/Documents/Git/tacos-zones/test/test_ata_formula.cpp > CMakeFiles/testata.dir/test_ata_formula.cpp.i

test/CMakeFiles/testata.dir/test_ata_formula.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Compiling CXX source to assembly CMakeFiles/testata.dir/test_ata_formula.cpp.s"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/spark046/Documents/Git/tacos-zones/test/test_ata_formula.cpp -o CMakeFiles/testata.dir/test_ata_formula.cpp.s

test/CMakeFiles/testata.dir/test_ata.cpp.o: test/CMakeFiles/testata.dir/flags.make
test/CMakeFiles/testata.dir/test_ata.cpp.o: test/test_ata.cpp
test/CMakeFiles/testata.dir/test_ata.cpp.o: test/CMakeFiles/testata.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --progress-dir=/home/spark046/Documents/Git/tacos-zones/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building CXX object test/CMakeFiles/testata.dir/test_ata.cpp.o"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT test/CMakeFiles/testata.dir/test_ata.cpp.o -MF CMakeFiles/testata.dir/test_ata.cpp.o.d -o CMakeFiles/testata.dir/test_ata.cpp.o -c /home/spark046/Documents/Git/tacos-zones/test/test_ata.cpp

test/CMakeFiles/testata.dir/test_ata.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Preprocessing CXX source to CMakeFiles/testata.dir/test_ata.cpp.i"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/spark046/Documents/Git/tacos-zones/test/test_ata.cpp > CMakeFiles/testata.dir/test_ata.cpp.i

test/CMakeFiles/testata.dir/test_ata.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Compiling CXX source to assembly CMakeFiles/testata.dir/test_ata.cpp.s"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/spark046/Documents/Git/tacos-zones/test/test_ata.cpp -o CMakeFiles/testata.dir/test_ata.cpp.s

test/CMakeFiles/testata.dir/test_print_ata.cpp.o: test/CMakeFiles/testata.dir/flags.make
test/CMakeFiles/testata.dir/test_print_ata.cpp.o: test/test_print_ata.cpp
test/CMakeFiles/testata.dir/test_print_ata.cpp.o: test/CMakeFiles/testata.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --progress-dir=/home/spark046/Documents/Git/tacos-zones/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building CXX object test/CMakeFiles/testata.dir/test_print_ata.cpp.o"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT test/CMakeFiles/testata.dir/test_print_ata.cpp.o -MF CMakeFiles/testata.dir/test_print_ata.cpp.o.d -o CMakeFiles/testata.dir/test_print_ata.cpp.o -c /home/spark046/Documents/Git/tacos-zones/test/test_print_ata.cpp

test/CMakeFiles/testata.dir/test_print_ata.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Preprocessing CXX source to CMakeFiles/testata.dir/test_print_ata.cpp.i"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/spark046/Documents/Git/tacos-zones/test/test_print_ata.cpp > CMakeFiles/testata.dir/test_print_ata.cpp.i

test/CMakeFiles/testata.dir/test_print_ata.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Compiling CXX source to assembly CMakeFiles/testata.dir/test_print_ata.cpp.s"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/spark046/Documents/Git/tacos-zones/test/test_print_ata.cpp -o CMakeFiles/testata.dir/test_print_ata.cpp.s

test/CMakeFiles/testata.dir/test_print_ata_formula.cpp.o: test/CMakeFiles/testata.dir/flags.make
test/CMakeFiles/testata.dir/test_print_ata_formula.cpp.o: test/test_print_ata_formula.cpp
test/CMakeFiles/testata.dir/test_print_ata_formula.cpp.o: test/CMakeFiles/testata.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --progress-dir=/home/spark046/Documents/Git/tacos-zones/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Building CXX object test/CMakeFiles/testata.dir/test_print_ata_formula.cpp.o"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT test/CMakeFiles/testata.dir/test_print_ata_formula.cpp.o -MF CMakeFiles/testata.dir/test_print_ata_formula.cpp.o.d -o CMakeFiles/testata.dir/test_print_ata_formula.cpp.o -c /home/spark046/Documents/Git/tacos-zones/test/test_print_ata_formula.cpp

test/CMakeFiles/testata.dir/test_print_ata_formula.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Preprocessing CXX source to CMakeFiles/testata.dir/test_print_ata_formula.cpp.i"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/spark046/Documents/Git/tacos-zones/test/test_print_ata_formula.cpp > CMakeFiles/testata.dir/test_print_ata_formula.cpp.i

test/CMakeFiles/testata.dir/test_print_ata_formula.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green "Compiling CXX source to assembly CMakeFiles/testata.dir/test_print_ata_formula.cpp.s"
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/spark046/Documents/Git/tacos-zones/test/test_print_ata_formula.cpp -o CMakeFiles/testata.dir/test_print_ata_formula.cpp.s

# Object files for target testata
testata_OBJECTS = \
"CMakeFiles/testata.dir/test_ata_formula.cpp.o" \
"CMakeFiles/testata.dir/test_ata.cpp.o" \
"CMakeFiles/testata.dir/test_print_ata.cpp.o" \
"CMakeFiles/testata.dir/test_print_ata_formula.cpp.o"

# External object files for target testata
testata_EXTERNAL_OBJECTS =

test/testata: test/CMakeFiles/testata.dir/test_ata_formula.cpp.o
test/testata: test/CMakeFiles/testata.dir/test_ata.cpp.o
test/testata: test/CMakeFiles/testata.dir/test_print_ata.cpp.o
test/testata: test/CMakeFiles/testata.dir/test_print_ata_formula.cpp.o
test/testata: test/CMakeFiles/testata.dir/build.make
test/testata: _deps/catch2-build/src/libCatch2Maind.a
test/testata: src/automata/libautomata.so
test/testata: /usr/lib64/libfmt.so.10.2.1
test/testata: _deps/catch2-build/src/libCatch2d.a
test/testata: test/CMakeFiles/testata.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --green --bold --progress-dir=/home/spark046/Documents/Git/tacos-zones/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "Linking CXX executable testata"
	cd /home/spark046/Documents/Git/tacos-zones/test && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/testata.dir/link.txt --verbose=$(VERBOSE)
	cd /home/spark046/Documents/Git/tacos-zones/test && /usr/bin/cmake -D TEST_TARGET=testata -D TEST_EXECUTABLE=/home/spark046/Documents/Git/tacos-zones/test/testata -D TEST_EXECUTOR= -D TEST_WORKING_DIR=/home/spark046/Documents/Git/tacos-zones/test -D TEST_SPEC= -D TEST_EXTRA_ARGS= -D TEST_PROPERTIES= -D TEST_PREFIX= -D TEST_SUFFIX= -D TEST_LIST=testata_TESTS -D TEST_REPORTER= -D TEST_OUTPUT_DIR= -D TEST_OUTPUT_PREFIX= -D TEST_OUTPUT_SUFFIX= -D TEST_DL_PATHS= -D CTEST_FILE=/home/spark046/Documents/Git/tacos-zones/test/testata_tests-b12d07c.cmake -P /home/spark046/Documents/Git/tacos-zones/_deps/catch2-src/extras/CatchAddTests.cmake

# Rule to build all files generated by this target.
test/CMakeFiles/testata.dir/build: test/testata
.PHONY : test/CMakeFiles/testata.dir/build

test/CMakeFiles/testata.dir/clean:
	cd /home/spark046/Documents/Git/tacos-zones/test && $(CMAKE_COMMAND) -P CMakeFiles/testata.dir/cmake_clean.cmake
.PHONY : test/CMakeFiles/testata.dir/clean

test/CMakeFiles/testata.dir/depend:
	cd /home/spark046/Documents/Git/tacos-zones && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/spark046/Documents/Git/tacos-zones /home/spark046/Documents/Git/tacos-zones/test /home/spark046/Documents/Git/tacos-zones /home/spark046/Documents/Git/tacos-zones/test /home/spark046/Documents/Git/tacos-zones/test/CMakeFiles/testata.dir/DependInfo.cmake "--color=$(COLOR)"
.PHONY : test/CMakeFiles/testata.dir/depend

