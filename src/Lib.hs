module Lib
    ( someFunc
    ) where

import GCLParser.Parser
import Z3.Monad

someFunc :: IO ()
someFunc = putStrLn "someFunc"
