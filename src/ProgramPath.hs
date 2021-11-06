module ProgramPath where

import Data.Maybe (fromMaybe)
import GCLParser.GCLDatatype (BinOp (..), Expr (..), Program (..), Stmt (..))
import WLP (simplifyExpr)

data ProgramPath a
  = TreePath
      { condition :: a,
        tStmts :: Maybe Stmt,
        option1 :: ProgramPath a,
        option2 :: ProgramPath a
      }
  | LinearPath
      { condition :: a,
        lStmts :: Stmt
      }
  | EmptyPath a -- Path that does not yet contain any statements or branches
  | InvalidPath --  Either because branch condition was unfeasible or because depth was too deep
  deriving (Show)

--
-- SECTION 1
--
-- The following functions are to build the path
--

-- Function that will transform a Program into a ProgramPath
constructPath :: Program -> ProgramPath Expr
constructPath program = _constructPath (listify $ stmt program)

-- Function that will transform a statement into a ProgramPath
_constructPath :: [Stmt] -> ProgramPath Expr
_constructPath ((IfThenElse expr ifStmt elseStmt) : stmts) = TreePath (LitB True) Nothing (injectExpression expr ifPath) (injectExpression (OpNeg expr) elsePath)
  where
    ifPath = _constructPath $ listify ifStmt ++ stmts
    elsePath = _constructPath $ listify elseStmt ++ stmts
_constructPath ((While expr stmt) : stmts) = tree
  where
    tree = TreePath (LitB True) Nothing skipWhile runs
    stmtTree = _constructPath $ listify stmt -- Construct a path of the inner statement. This is required because there may be nested special environments.
    skipWhile = injectExpression (OpNeg expr) (_constructPath stmts)
    runs = combinePaths stmtTree (TreePath expr Nothing skipWhile runs) -- Construct paths for when the while runs
_constructPath (Assert invar : w@(While expr stmt) : stmts) = tree -- A loop with an invariant was found
  where
    -- When invariant is used, add a path that has the artificial invariant structure (Seq Assert While) and append the error checking paths after it
    useInvariantPath = combinePaths (_constructPath [Seq (Assert invar) w]) (errorCheckingPath (_constructPath stmts))
    tree = if hasInnerWhile then _constructPath (w : stmts) else useInvariantPath
    -- Check if the while has inner while. If it has another loop, we will not use the invariant, as the inner while may not be annoted.
    hasInnerWhile = hasInnerWhile' $ listify stmt -- Create statement list
    -- Check if statement list has while
    hasInnerWhile' (While {} : xs) = True
    hasInnerWhile' (x : xs) = hasInnerWhile' xs
    hasInnerWhile' [] = False
_constructPath ((Block vars stmt) : stmts) = error $ "Found unfiltered block! \r\n" ++ show stmt -- Block should be filtered out during splitList
_constructPath (stmt : stmts) = combinePaths (LinearPath (LitB True) stmt) $ _constructPath stmts
_constructPath [] = EmptyPath (LitB True)

-- Construct paths that will be evaluated when exc is not 0.
-- They can be used to find what kind of error was produced, as they explicitly set the corresponding exception code.
-- Note that they add an Assert False, thus they don't further evaluate the noErrorPath and are a form of early stopping when there is an exception.
errorCheckingPath :: ProgramPath Expr -> ProgramPath Expr
errorCheckingPath noErrorPath = TreePath (LitB True) Nothing t1 (injectExpression testNoException noErrorPath)
  where
    assignPath x = LinearPath (BinopExpr Equal (Var "exc") (LitI x)) (Seq (Assign "exc" (LitI x)) (Assert (LitB False)))
    testNoException = BinopExpr Equal (Var "exc") (LitI 0)
    t1 = TreePath (LitB True) Nothing (assignPath 1) t2
    t2 = TreePath (LitB True) Nothing (assignPath 2) (assignPath 3)

-- Turns seq into a list of statements
unrollSeq :: Stmt -> [Stmt]
unrollSeq (Seq s1 s2) = unrollSeq s1 ++ unrollSeq s2
unrollSeq s = [s]

-- Turns statement into list of statements that are either: while, if, vardecl, pure seq, single statement
listify :: Stmt -> [Stmt]
listify allStmts = splitList (unrollSeq allStmts)

-- Turns a list of statements into a list of statements that are either: while, if, vardecl, pure seq, single statement
splitList :: [Stmt] -> [Stmt]
splitList allStmts = splitList' allStmts []

-- Turns a list of statements into a list of statements that are either: while, if, vardecl, pure seq, single statement
-- First parameter is list of single statements, second parameter is accumulator: list of pure single statements that can finally be put into a list
-- When the first non-pure statement is found, the accumulator will be rolled into a seq, added to the result list, then the unpure statement will be put in the list, then it will evaluate the other statements
splitList' :: [Stmt] -> [Stmt] -> [Stmt]
splitList' [] [] = []
splitList' [] stmts = rollSeqr stmts
splitList' (w@While {} : statements) stmts = rollSeqr stmts ++ (w : splitList statements)
splitList' (Assert e : w@While {} : statements) stmts = rollSeqr stmts ++ [Assert e] ++ (w : splitList statements) -- Loop invariant found
splitList' (w@IfThenElse {} : statements) stmts = rollSeqr stmts ++ (w : splitList statements)
splitList' ((Block _ stmt) : statements) stmts = splitList' (listify stmt ++ statements) stmts -- Take code out of the block, and process as its own entity
splitList' (s : statements) stmts = splitList' statements (s : stmts)

-- Rolls a list of statements into a Seq, where the begin of the Seq is on the right of the list
rollSeqr :: [Stmt] -> [Stmt]
rollSeqr [] = []
rollSeqr stmts = [rollSeql $ reverse stmts]

-- Rolls a list of statements into a Seq, where the begin of the Seq is on the left of the list
rollSeql :: [Stmt] -> Stmt
rollSeql [s] = s
rollSeql (s : ss) = Seq s (rollSeql ss)
rollSeql [] = error "Cannot roll empty array"

-- Injects the given expression into the condition for the given path
injectExpression :: Expr -> ProgramPath Expr -> ProgramPath Expr
injectExpression expr (LinearPath cond stmts) = LinearPath (BinopExpr And cond expr) stmts
injectExpression expr (TreePath cond stmts option1 option2) = TreePath (BinopExpr And cond expr) stmts option1 option2
injectExpression expr (EmptyPath cond) = EmptyPath (BinopExpr And cond expr)
injectExpression _ InvalidPath = InvalidPath

-- Utility function that can combine two ProgramPaths into a single ProgramPath
combinePaths :: ProgramPath Expr -> ProgramPath Expr -> ProgramPath Expr
combinePaths (LinearPath condA stmtA) (LinearPath condB stmtB) = LinearPath (simplifyExpr (BinopExpr And condA condB)) (Seq stmtA stmtB)
combinePaths (LinearPath condA lin) (TreePath condB tStmts option1 option2) = TreePath (simplifyExpr (BinopExpr And condA condB)) newStmts option1 option2 where newStmts = maybe (Just lin) (Just . Seq lin) tStmts
combinePaths (TreePath cond tStmts option1 option2) linpath@LinearPath {} = TreePath cond tStmts (combinePaths option1 linpath) (combinePaths option2 linpath)
combinePaths (TreePath cond tStmts option1 option2) treepath@TreePath {} = TreePath cond tStmts (combinePaths option1 treepath) (combinePaths option2 treepath)
combinePaths (EmptyPath cond) otherPath = injectExpression cond otherPath
combinePaths otherPath empty@(EmptyPath cond) = combinePaths empty otherPath
combinePaths _ _ = InvalidPath

--
-- SECTION 2
--
-- The following functions are for finding and removing invalid paths, and
-- turning the tree to a tree of finite length.
--

--Wrapper for actual function, so it wont keep evaluating the infinite structure
removePaths :: ProgramPath Expr -> Int -> (ProgramPath Expr, Int)
removePaths tree depth
  | depth <= 0 = (InvalidPath, 0)
  | otherwise = _removePaths tree depth

_removePaths :: ProgramPath Expr -> Int -> (ProgramPath Expr, Int)
_removePaths (TreePath _ _ InvalidPath InvalidPath) depth = (InvalidPath, 0) -- Prune a branch if both branches are invalid
_removePaths (TreePath cond tStmts pathA pathB) depth
  | remDepth < 0 = (InvalidPath, 0) -- In this case all preceding statements are longer than what happens after branching, so K is exceeded anyway
  | otherwise = pruneInvalidBranch (TreePath cond tStmts newA newB) -- Evaluate both paths. If both turn out to be unfeasible this node is pruned as well
  where
    baseDepth = splitDepth tStmts depth -- How many statements happen before the branch
    remDepth = depth - baseDepth -- The depth remaining after the preceding statements
    (newA, newACount) = removePaths pathA remDepth -- Evaluate path A, see if it is feasible given the depth
    (newB, newBCount) = removePaths pathB remDepth -- Evaluate path B, see if it is feasible given the depth
    pruneInvalidBranch (TreePath cond _ InvalidPath InvalidPath) = (InvalidPath, 0) -- Invalidate path if both branches are unfeasible
    --
    pruneInvalidBranch tree@(TreePath _ _ _ InvalidPath) = (tree, newACount)
    pruneInvalidBranch tree@(TreePath _ _ InvalidPath _) = (tree, newBCount)
    pruneInvalidBranch tree = (tree, newACount + newBCount)
_removePaths linpath@LinearPath {} depth
  | depth < totalDepth linpath depth = (InvalidPath, 0) -- Make path unfeasible if it exceeds the depth
  | otherwise = (linpath, 1)
_removePaths InvalidPath _ = (InvalidPath, 0)
_removePaths (EmptyPath _) _ = (InvalidPath, 0) -- Invalidate empty paths

-- Wrapper for actual function, so it wont keep evaluating the infinite structure
flagInvalid :: ProgramPath Expr -> Int -> ProgramPath Expr
flagInvalid tree depth
  | depth <= 0 = InvalidPath
  | otherwise = _flagInvalid tree depth

_flagInvalid :: ProgramPath Expr -> Int -> ProgramPath Expr
_flagInvalid (TreePath cond tStmts pathA pathB) depth
  | remDepth < 0 = InvalidPath -- Invalidate branch node if its statements are longer than the allowed depth
  | otherwise = TreePath cond tStmts (flagInvalid pathA remDepth) (flagInvalid pathB remDepth)
  where
    baseDepth = splitDepth tStmts depth -- How many statements happen before the branch
    remDepth = depth - baseDepth -- The depth remaining after the preceding statements
_flagInvalid linpath@LinearPath {} depth
  | depth < totalDepth linpath depth = InvalidPath -- Make path unfeasible if it exceeds the depth
  | otherwise = linpath
_flagInvalid InvalidPath _ = InvalidPath
_flagInvalid (EmptyPath _) _ = InvalidPath -- Invalidate empty paths
--
-- SECTION 4
--
-- The following functions are used to calculate properties over, and print information about the tree
--

countBranches :: Num p => ProgramPath a -> p
countBranches (TreePath _ _ option1 option2) = countBranches option1 + countBranches option2
countBranches InvalidPath = 0
countBranches (EmptyPath _) = 0
countBranches LinearPath {} = 1

-- Returns the number of invalid nodes for a path of FIXED LENGTH
numInvalid :: Num p => ProgramPath a -> p
numInvalid (TreePath _ _ option1 option2) = numInvalid option1 + numInvalid option2
numInvalid InvalidPath = 1
numInvalid _ = 0

-- Returns the number of nodes with a condition of false for a path of FIXED LENGTH
numConditionFalse :: Num p => ProgramPath Expr -> p
numConditionFalse t@(TreePath cond _ option1 option2)
  | cond == LitB False = countBranches t
  | otherwise = numConditionFalse option1 + numConditionFalse option2
numConditionFalse InvalidPath = 0
numConditionFalse (EmptyPath _) = 0
numConditionFalse (LinearPath cond _) = if cond == LitB False then 1 else 0

-- Note that this function assumes that all ifs and whiles have been removed from the path
countStatements :: Num p => Stmt -> p
countStatements (Seq a b) = countStatements a + countStatements b
countStatements (Block _ stmts) = countStatements stmts
countStatements _ = 1

-- Print the whole tree for the given program path
-- Wrapper for actual function, so it wont keep evaluating the infinite structure
printTree :: Show a => ProgramPath a -> Int -> String
printTree tree depth = _printTree tree depth depth

_printTree :: Show a => ProgramPath a -> Int -> Int -> String
_printTree tree depth k
  | depth < 0 = "Depth exceeded"
  | otherwise = __printTree tree depth k

__printTree :: Show a => ProgramPath a -> Int -> Int -> String
__printTree InvalidPath _ _ = "INVALID PATH FOUND"
__printTree (EmptyPath _) _ _ = "LOOSE EMPTY PATH FOUND"
__printTree (LinearPath cond a) depth k = "[" ++ show cond ++ "]" ++ show a
  where
    aDepth = totalDepth (LinearPath cond a) depth
    remDepth = depth - aDepth
__printTree (TreePath cond tStmts option1 option2) depth k =
  tabs
    ++ show tStmts
    ++ "\n"
    ++ tabs
    ++ "Branch1:\n"
    ++ tabs
    ++ _printTree option1 remDepth (k + 1)
    ++ "\n"
    ++ tabs
    ++ "Branch2:\n"
    ++ _printTree option2 remDepth (k + 1) -- Add k+1, because Nothing as tStmts may lead to it thinking it is on the same level
  where
    baseDepth = splitDepth tStmts depth
    remDepth = depth - baseDepth
    tabs = replicate (2 * (k - depth)) ' ' -- Tabs for same level

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
_totalDepth (TreePath _ tStmts option1 option2) depth = baseDepth + max (totalDepth option1 remDepth) (totalDepth option2 remDepth) --Length of a branching path is length of preceding statements + max(length branch 1, length branch 2)
  where
    baseDepth = splitDepth tStmts depth -- Length of preceding statements
    remDepth = depth - baseDepth -- Depth remaining to explore after the preceding statements
_totalDepth linpath@LinearPath {} depth = totalDepth linpath depth -- If this function was called directly, this will send a linear path back to the wrapper

-- Utility function that can check the depth of a Maybe Stmt (0 if none is present, n if there is a Stmt)
splitDepth :: Maybe Stmt -> Int -> Int
splitDepth tStmts depth = maybe 0 countStatements tStmts
