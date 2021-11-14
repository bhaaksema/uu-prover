module ProgramPathOps where

import GCLParser.GCLDatatype
import ProgramPath

--
-- The following functions are used to calculate properties over, and print information about the tree
--

countBranches :: Num p => ProgramPath a -> p
countBranches (BranchPath _ _ option1 option2) = countBranches option1 + countBranches option2
countBranches (AnnotedWhilePath _ _ option1 option2) = countBranches option1 * countBranches option2
countBranches (TryCatchPath option1 _ option2 option3) = countBranches option1 * countBranches option2 * countBranches option3
countBranches InvalidPath = 0
countBranches (EmptyPath _) = 0
countBranches LinearPath {} = 1

-- Returns the number of nodes with a condition of false for a path of FIXED LENGTH
numConditionFalse :: Num p => ProgramPath Expr -> p
numConditionFalse t@(BranchPath cond _ option1 option2)
  | cond == LitB False = countBranches t
  | otherwise = numConditionFalse option1 + numConditionFalse option2
numConditionFalse (AnnotedWhilePath _ _ option1 option2) = numConditionFalse option1 * numConditionFalse option2
numConditionFalse (TryCatchPath option1 _ option2 option3) = numConditionFalse option1 * numConditionFalse option2 * numConditionFalse option3
numConditionFalse InvalidPath = 0
numConditionFalse (EmptyPath _) = 0
numConditionFalse (LinearPath cond _) = if cond == LitB False then 1 else 0

-- Note that this function assumes that all ifs and whiles have been removed from the path
countStatements :: Num p => Stmt -> p
countStatements (Seq a b) = countStatements a + countStatements b
countStatements (Block _ stmts) = countStatements stmts
countStatements (While _ stmts) = countStatements stmts
countStatements _ = 1

-- Get the length of the longest branched path
-- Wrapper for actual function, so it wont keep evaluating the infinite structure
-- Note that linear paths should be allowed to be evaluated further than depth, as otherwise we won't know if they are too long. If they are too long however the returned value will be > the given depth, so it can be derived that this path is too long
totalDepth :: ProgramPath a -> Int -> Int
totalDepth (LinearPath _ stmts) depth = countStatements stmts -- Depth of a linear path is just counting the statements statement
totalDepth path depth -- Wrapper for handling of non-linear ProgramPath structure
  | depth <= 0 = depth -- Cut off when max depth was reached
  | otherwise = _totalDepth path depth

_totalDepth :: ProgramPath a -> Int -> Int
_totalDepth InvalidPath depth = 0 -- Invalid path has no depth
_totalDepth (EmptyPath _) depth = 0 -- Empty path has no depth
_totalDepth (BranchPath _ tStmts option1 option2) depth = baseDepth + max (totalDepth option1 remDepth) (totalDepth option2 remDepth) --Length of a branching path is length of preceding statements + max(length branch 1, length branch 2)
  where
    baseDepth = splitDepth tStmts depth -- Length of preceding statements
    remDepth = depth - baseDepth -- Depth remaining to explore after the preceding statements
_totalDepth (AnnotedWhilePath _ _ option1 option2) depth = baseDepth + totalDepth option1 remDepth --Length of a while path is length of inner statements + length of next statements
  where
    baseDepth = totalDepth option2 depth -- Length of preceding statements
    remDepth = depth - baseDepth -- Depth remaining to explore after the preceding statements
_totalDepth (TryCatchPath option1 _ option2 option3) depth = depth1 * depth2 * depth3
  where
    depth3 = totalDepth option3 depth -- Length of preceding statements
    depth2 = totalDepth option2 (depth - depth3) - 1 -- Length of catch statements, -1 because we inject a exc:=0 statement
    depth1 = totalDepth option1 (depth - depth3 - depth2) -- Length of try statements
_totalDepth linpath@LinearPath {} depth = totalDepth linpath depth -- If this function was called directly, this will send a linear path back to the wrapper

-- Utility function that can check the depth of a Maybe Stmt (0 if none is present, n if there is a Stmt)
splitDepth :: Maybe Stmt -> Int -> Int
splitDepth tStmts depth = maybe 0 countStatements tStmts
