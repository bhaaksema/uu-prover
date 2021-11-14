# WLP-based Bounded Symbolic Verifier

## Prerequisites
Compilation requires the following packages:
```
haskell-stack libz3-dev
```

Make sure you are running a recent version of `stack`, you can always try to upgrade the binary:
```
stack upgrade
```

While it is possible to use stack to build the tool and the test/benchmark suites, it is not necessary as stack will automatically do so when required.

## Basic Usage
```
stack run -- [-K <value>] [-file <file>] [-wlp] [-path] [-Hoff] [-noExc]
```
- `-K <value>`: Specifies the depth parameter K, only finite paths up till this length are taken into account.
- `-file <file>`: Specifies the GCL source code file to be verified.
- `-wlp`: Enable the displaying of every calculated wlp. Additionally, if a counter-example is found, this flag will show in which wlp the counter-example occurred.
- `-path`: Enable the displaying of every encountered path.
- `-Hoff`: Disables our preprocessing heuristic, which is able to prune infeasible paths.
- `-noExc`: Disables checking for unsafe expressions. Will let the verifier accept a program that would otherwise be rejected because of an exception.

## Test Suite
Checks the soundness of the verifier by finding the minimal accepting value of depth K for all combinations of benchmark files in `input/bench/` and `N = [2..10]`. Will throw an `empty list` error when the verifier finds a counterexample for one of the combinations of program F, parameter N and depth K.
```
stack test
```

## Benchmark Suite
Uses the Criterion benchmark suite to perform performance measurements on the files in `input/bench/`. It is recommended to run the benchmarks individually with the following command where `<pattern>` is the name of a file in the mentioned folder.
```
stack bench --benchmark-arguments "<pattern> -m prefix -o <name>.html"
```
