import Criterion.Main
import ProgramPath (run)

main = defaultMain [
    bench "bsort" $ nfIO (run "input/bench/bsort.gcl"),
    bench "divByN" $ nfIO (run "input/bench/divByN.gcl"),
    bench "find12" $ nfIO (run "input/bench/find12.gcl"),
    bench "memberOf" $ nfIO (run "input/bench/memberOf.gcl"),
    bench "min" $ nfIO (run "input/bench/min.gcl"),
    bench "pullUp" $ nfIO (run "input/bench/pullUp.gcl")
  ]
