module Evaluator where

import Control.Monad (when)
import Data.Map (empty, keys, toList)
import GCLParser.GCLDatatype
import GCLParser.Parser (parseGCLfile)
import ProgramPath
import System.Environment (getArgs)
import WLP (findLocvars, numExprAtoms)
import Z3.Monad (Result (..), astToString, evalZ3)

-- The following functions will run the 'main' program and output the required information
-- main loads the file and puts the ParseResult Program through the following functions
arguments :: [[Char]] -> (Int, [Char], Bool, Bool)
arguments [] = (10, "input/test/reverse.gcl", False, False)
arguments ("-K" : arg : xs) = (read arg, a2, a3, a4)
  where
    (_, a2, a3, a4) = arguments xs
arguments ("-file" : arg : xs) = (a1, arg, a3, a4)
  where
    (a1, _, a3, a4) = arguments xs
arguments ("-wlp" : xs) = (a1, a2, True, a4)
  where
    (a1, a2, _, a4) = arguments xs
arguments ("-path" : xs) = (a1, a2, a3, True)
  where
    (a1, a2, a3, _) = arguments xs
arguments (x : xs) = arguments xs

run :: IO ()
run = do
  args <- getArgs
  let parsedArgs@(_, file, _, _) = arguments args
  program <- parseGCLfile file
  evaluateProgram program parsedArgs

--Will return if all of the statements were correctly verified
mapUntilSat :: ((Expr, ProgramPath Expr) -> (IO Result, ProgramPath Expr, Expr)) -> [(Expr, ProgramPath Expr)] -> IO (Result, ProgramPath Expr, Expr)
mapUntilSat f [] = return (Unsat, EmptyPath (LitB True), LitB True)
mapUntilSat f (x : xs) = do
  let (r, path, wlp) = f x
  result <- r
  case result of
    Sat -> return (Sat, path, wlp)
    Unsat -> mapUntilSat f xs
    Undef -> do
      (others, otherPath, otherWlp) <- mapUntilSat f xs
      case others of
        Sat -> return (Sat, otherPath, otherWlp)
        _ -> return (Undef, path, wlp)

evaluateProgram :: Either a Program -> (Int, [Char], Bool, Bool) -> IO ()
evaluateProgram (Left _) _ = putStrLn "Unable to parse program"
evaluateProgram (Right program) (k, file, printWlp, printPath) = do
  let path = constructPath program
  let locVars = findLocvars (stmt program)
  let flaggedPath = flagInvalid path k

  let pathsTooLong = numInvalid flaggedPath
  putStrLn ("Results when using k=" ++ show k ++ " on " ++ file ++ ":")
  putStrLn []
  putStrLn ("Found " ++ show (countBranches flaggedPath) ++ " paths.")
  putStrLn ("Of these paths, at least " ++ show pathsTooLong ++ " are infeasible as they are too long.")
  putStrLn []
  let clearedPath = removePaths path k
  let cantBranch = numConditionFalse clearedPath
  putStrLn ("Reduced structure to " ++ show (countBranches clearedPath) ++ " paths.")
  putStrLn ("Of these paths, " ++ show cantBranch ++ " can be pruned as their branch condition is the literal False. (TODO)")

  -- Print path if the argument -path was specified
  putStrLn []
  when printPath $ putStrLn "The path is:"
  when printPath $
    putStrLn (printTree clearedPath k)
  putStrLn "Evaluating the reduced structure gives:"
  putStrLn []

  -- Create a map with all the variables and an initial value of (Var name)
  let (vars, varTypes) = foldl addExprVariable (empty, empty) (input program ++ output program ++ locVars)

  -- Calculate the wlp and initial variable values over the tree
  let wlpsInfo = calcWLP clearedPath vars
  let wlps = map fst wlpsInfo
  putStrLn "All defined variables are are:"
  print (keys vars)
  --putStrLn "Initial variable values are:"
  --print (toList vars')
  putStrLn "Z3 variables that will be created created to solve:"
  print $
    mutatedVariables vars
  putStrLn []

  putStrLn $
    "Found " ++ show (length wlps) ++ " WLPs making for a total of " ++ show (sum (map numExprAtoms wlps)) ++ " atoms."

  -- Print wlp and z3 script if -wlp was specified
  when printWlp $ putStrLn "The WLPs are:"
  when printWlp $ print wlps
  --when printWlp $ putStrLn "The corresponding z3 scripts is:"
  --script <- evalZ3 $ astToString =<< z3Script (OpNeg wlp) (vars, varTypes)
  --when printWlp $ putStrLn script
  putStrLn []

  -- Print the result of the verification
  (final, finalPath, finalWlp) <- mapUntilSat (\(wlp, path) -> (verifyExpr (OpNeg wlp) (vars, varTypes), path, wlp)) wlpsInfo
  case final of
    Unsat -> putStrLn "No counter examples for this program could be found."
    Undef -> putStrLn "At least one of the paths returned Undef, but no counter examples for this program could be found."
    Sat -> do
      putStrLn ("Found this counterexample in the path: " ++ show finalPath)
      putStrLn "The corresponding z3 scripts is:"
      script <- evalZ3 $ astToString =<< z3Script (OpNeg finalWlp) (vars, varTypes)
      putStrLn script
