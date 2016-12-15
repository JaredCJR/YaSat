# A template C++ Makefile for your SAT solver.

# Debugging flags
FLAGS=-Wall -O0 -g3 -std=c++14 -Ddebug

# Optimizing flags
#FLAGS=-Wall -Ofast -std=c++14

# List all the .o files you need to build here
OBJS=parser.o sat.o

# This is the name of the executable file that gets built.  Please
# don't change it.
EXENAME=yasat

# Compile targets
all: $(EXENAME)
$(EXENAME): $(OBJS)
	g++ $(FLAGS) $^ -lz -o $(EXENAME)
%.o: %.cpp
	g++ -c $(FLAGS) $^ -o $@

# Add more compilation targets here
test: $(EXENAME)
	./yasat benchmarks/UNSAT/tiny/rand5_30.cnf

gdb: $(EXENAME)
	gdbtui -x gdb.txt --args  ./yasat benchmarks/Sample_benchmarks_for_Milestone_2/aim-50-1_6-yes1-1.cnf

gdb_2: $(EXENAME)
	gdbtui -x gdb.txt --args  ./yasat benchmarks/uf_SAT/uf100-0542.cnf


# The "phony" `clean' compilation target.  Type `make clean' to remove
# your object files and your executable.
.PHONY: clean
clean:
	rm -rf $(OBJS) $(EXENAME)
