# WLP-based Bounded Symbolic Verifier
http://www.cs.uu.nl/docs/vakken/pv/2122/stuffs/PVproject_2122.pdf

## Prerequisites
Compilation requires the following packages:
```
haskell-stack libz3-dev
```

## Basic Usage
```
stack run -- [-K <value>] [-file <file>] [-wlp] [-path] [-Hoff] [-noExc]
```

## Test Suite
Checks the soundness of the verifier by finding the minimal accepting value of depth `K` for all combinations of benchmark files in `input/bench/` and `N = [2..10]`. Will throw an `empty list` error when the verifier finds a counterexample for one of the combinations of program `F`, parameter `N` and depth `K`.
```
stack test
```

## Benchmark Suite
Uses the Criterion benchmark suite to perform performance measurements on the files in `input/bench/`. It is reccomended to run the benchmarks individually with the following command where `<pattern>` is the name of a file in the mentioned folder.
```
stack bench --benchmark-arguments "<pattern> -m prefix -o bench.html"
```
