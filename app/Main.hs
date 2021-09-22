module Main where

import Lib
import POC

--main :: IO () --Removed because POC.run has different type
main = do r <- run
          putStrLn (show r)
