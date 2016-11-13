#!/bin/bash
make clean && make
echo ================================================================
echo ================================================================
echo "SAT"
./yasat benchmarks/SAT/sanity/sanity2.cnf
./yasat benchmarks/SAT/sanity/sanity3.cnf

./yasat benchmarks/SAT/tiny/rand5_10.cnf
./yasat benchmarks/SAT/tiny/rand10_20.cnf
echo ================================================================
echo ================================================================
echo "UNSAT"
./yasat benchmarks/UNSAT/sanity/sanity4.cnf
./yasat benchmarks/UNSAT/sanity/sanity5.cnf

./yasat benchmarks/UNSAT/tiny/rand5_30.cnf
./yasat benchmarks/UNSAT/tiny/rand10_50.cnf
echo ================================================================
echo ================================================================
echo "large test"
time ./yasat benchmarks/large/sat100.cnf
time ./yasat benchmarks/large/sat250.cnf
time ./yasat benchmarks/large/unsat250.cnf
