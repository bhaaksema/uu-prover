# WLP-based Bounded Symbolic Verifier
http://www.cs.uu.nl/docs/vakken/pv/2122/stuffs/PVproject_2122.pdf

## Prerequisites
Compilation requires the following packages:
```
haskell-stack libz3-dev
```

## Basic Usage
```
stack run -- [-K <value>] [-file <file>] [-wlp] [-path]
```

## Test Suite
Runs the verifier on all files in `/test/input` for K = [0..20].
```
stack test
```

## Benchmark Suite
Uses the Criterion benchmark suite to perform performance measurements on the files in `/bench/input` for N = [2..10] and K = 5.
```
stack bench
```
