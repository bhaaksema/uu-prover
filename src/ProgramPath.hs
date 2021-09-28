module ProgramPath where

import Data.Maybe (fromMaybe)
import GCLParser.GCLDatatype
import GCLParser.Parser (ParseResult, parseGCLfile)
import Z3.Monad

data ProgramPath
  = TreePath
      { stmts :: Maybe Stmt,
        option1 :: ProgramPath,
        option2 :: ProgramPath
      }
  | LinearPath Stmt
  | InvalidPath -- Either because branch condition was unfeasible or because depth was too deep
  deriving (Show)

--Function that will transform a Program into a ProgramPath
constructPath :: Program -> ProgramPath
constructPath program = _constructPath (stmt program)

--Function that will transform a statement into a Programpath
_constructPath :: Stmt -> ProgramPath
_constructPath (IfThenElse expr ifStmt elseStmt) = TreePath Nothing (_constructPath ifStmt) (_constructPath elseStmt)
_constructPath (While expr stmt) = TreePath Nothing (_constructPath stmt) (_constructPath (Seq stmt (While expr stmt)))
_constructPath (Seq stmt nextStmt) = combinePaths (_constructPath stmt) (_constructPath nextStmt)
_constructPath stmt = LinearPath stmt

--Utility function that can combine two ProgramPaths into a single ProgramPath
combinePaths :: ProgramPath -> ProgramPath -> ProgramPath
combinePaths (LinearPath stmtA) (LinearPath stmtB) = LinearPath (Seq stmtA stmtB)
combinePaths (LinearPath lin) (TreePath stmts option1 option2) = TreePath newStmts option1 option2 where newStmts = maybe (Just lin) (Just . Seq lin) stmts
combinePaths (TreePath stmts option1 option2) (LinearPath lin) = TreePath stmts (combinePaths option1 l) (combinePaths option2 l) where l = LinearPath lin
combinePaths _ _ = InvalidPath

--Get the length of the longest branched path
--Wrapper for actual function, so it wont keep evaluating the infinite structure
--Note that linear paths should be allowed to be evaluated further than depth, as otherwise we won't know if they are too long. If they are too long however the returned value will be > the given depth, so it can be derived that this path is too long
totalDepth :: ProgramPath -> Int -> Int
totalDepth (LinearPath (Seq a b)) depth = aDepth + totalDepth (LinearPath b) remDepth --The length of a Seq is the length of the first statement + length of the second statement (where second statement should not be evaluated further than depth - length of first statement)
  where
    aDepth = totalDepth (LinearPath a) depth --Length of the first statement
    remDepth = depth - aDepth --Length remaining for the second statement
totalDepth (LinearPath _) depth = 1 --Depth of a single statement
totalDepth path depth --Wrapper for handeling of non-linear ProgramPath structure
  | depth <= 0 = depth --Cut off when max depth was reached
  | otherwise = _totalDepth path depth

_totalDepth :: ProgramPath -> Int -> Int
_totalDepth InvalidPath depth = 0 --Invalid path has no depth
_totalDepth (TreePath stmts option1 option2) depth = baseDepth + max (totalDepth option1 remDepth) (totalDepth option2 remDepth) --Length of a branching path is length of preceding statements + max(length branch 1, length branch 2)
  where
    baseDepth = splitDepth stmts depth --Length of preceding statements
    remDepth = depth - baseDepth --Depth remaining to explore after the preceding statements
_totalDepth linpath@(LinearPath lin) depth = totalDepth linpath depth --If this function was called directly, this will send a linear path back to the wrapper

--Utility function that can check the depth of a Maybe Stmt (0 if none is present, n if there is a Stmt)
splitDepth :: Maybe Stmt -> Int -> Int
splitDepth stmts depth = maybe 0 (\s -> totalDepth (LinearPath s) depth) stmts

--Wrapper for actual function, so it wont keep evaluating the infinite structure
removePaths :: ProgramPath -> Int -> ProgramPath
removePaths tree depth
  | depth <= 0 = InvalidPath
  | otherwise = _removePaths tree depth

_removePaths :: ProgramPath -> Int -> ProgramPath
_removePaths (TreePath _ InvalidPath InvalidPath) depth = InvalidPath --Prune a branch if both branches are invalid
_removePaths (TreePath stmts pathA pathB) depth
  | remDepth < 0 = InvalidPath --In this case all preceding statements are longer than what happens after branching, so K is exceeded anyway
  | otherwise = pruneInvalidBranch (TreePath stmts newA newB) --Evaluate boths paths. If both turn out to be unfeasable this node is pruned as well
  where
    baseDepth = splitDepth stmts depth --How many statements happen before the branch
    remDepth = depth - baseDepth --The depth remaining after the preceding statements
    newA = removePaths pathA remDepth --Evaluate path A, see if it is feasible given the depth
    newB = removePaths pathB remDepth --Evaluate path B, see if it is feasible given the depth
    pruneInvalidBranch (TreePath _ InvalidPath InvalidPath) = InvalidPath --Invalidate path if both branches are unfeasible
    --
    pruneInvalidBranch (TreePath (Just stmts) InvalidPath (LinearPath stmt)) = LinearPath (Seq stmts stmt) --Linearise a branch if only one of the paths is feasible
    pruneInvalidBranch (TreePath Nothing InvalidPath linpath@(LinearPath _)) = linpath --Linearise a branch if only one of the paths is feasible
    pruneInvalidBranch (TreePath stmts linpath@(LinearPath _) InvalidPath) = pruneInvalidBranch (TreePath stmts InvalidPath linpath) --Swap arguments and run previous case
    --
    pruneInvalidBranch (TreePath (Just stmts) InvalidPath (TreePath (Just stmt) option1 option2)) = TreePath (Just (Seq stmts stmt)) option1 option2 --Combine branches to one big branch
    pruneInvalidBranch (TreePath (Just stmts) InvalidPath (TreePath Nothing option1 option2)) = TreePath (Just stmts) option1 option2 --Combine branches to one big branch
    pruneInvalidBranch (TreePath Nothing InvalidPath treepath@TreePath {}) = treepath --Linearise a branch if only one of the paths is feasible
    pruneInvalidBranch (TreePath stmts treepath@TreePath {} InvalidPath) = pruneInvalidBranch (TreePath stmts InvalidPath treepath) --Swap arguments and run previous case
    --
    pruneInvalidBranch tree = tree
_removePaths linpath@(LinearPath lin) depth
  | depth < totalDepth linpath depth = InvalidPath --Make path unfeasible if it exceeds the depth
  | otherwise = linpath
_removePaths InvalidPath _ = InvalidPath

--Print the whole tree for the given program path
--Wrapper for actual function, so it wont keep evaluating the infinite structure
printTree :: ProgramPath -> Int -> String
printTree tree depth
  | depth < 0 = "Depth exceeded"
  | otherwise = _printTree tree depth

_printTree :: ProgramPath -> Int -> String
_printTree InvalidPath _ = "INVALID PATH FOUND"
_printTree (LinearPath (Seq a b)) depth = printTree (LinearPath a) depth ++ printTree (LinearPath b) remDepth
  where
    aDepth = totalDepth (LinearPath a) depth
    remDepth = depth - aDepth
_printTree (LinearPath l) _ = show l
_printTree (TreePath stmts option1 option2) depth = show stmts ++ "\n" ++ tabs ++ "Branch1:\n" ++ tabs ++ printTree option1 remDepth ++ "\n" ++ tabs ++ "Branch2:\n" ++ tabs ++ printTree option2 remDepth
  where
    baseDepth = splitDepth stmts depth
    remDepth = depth - baseDepth
    tabs = replicate (20 - depth) '\t'

-- main loads the file and puts the ParseResult Program through the following functions
run = do
  program <- parseGCLfile "min.gcl"
  either (\p -> putStrLn "Unable to parse") (\p -> print (totalDepth (constructPath p) 20)) program
  either (\p -> putStrLn "Unable to parse") (\p -> putStrLn (printTree (constructPath p) 20)) program
  either (\p -> putStrLn "Unable to parse") (\p -> print (totalDepth (removePaths (constructPath p) 20) 20)) program
  either (\p -> putStrLn "Unable to parse") (\p -> putStrLn (printTree (removePaths (constructPath p) 20) 20)) program

--print (constructPath <$> program)