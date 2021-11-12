module ProgramPath where

import Data.Maybe (fromMaybe)
import GCLParser.GCLDatatype (BinOp (..), Expr (..), Program (..), Stmt (..))
import GeneralTypes
import WLP (simplifyExpr)

data ProgramPath a
  = BranchPath
      { condition :: a,
        tStmts :: Maybe Stmt,
        option1 :: ProgramPath a,
        option2 :: ProgramPath a
      }
  | LinearPath
      { condition :: a,
        lStmts :: Stmt
      }
  | AnnotedWhilePath
      { invariant :: a,
        guard :: a,
        innerPath :: ProgramPath a,
        nextPath :: ProgramPath a
      }
  | TryCatchPath
      { try :: ProgramPath a,
        exceptionLocalname :: String,
        catch :: ProgramPath a,
        nextPath :: ProgramPath a
      }
  | EmptyPath a -- Path that does not yet contain any statements or branches
  | InvalidPath --  Either because branch condition was unfeasible or because depth was too deep
  deriving (Show)

type RemainingPathCount = Int

--
-- SECTION 1
--
-- The following functions are to build the path
--

-- Function that will transform a Program into a ProgramPath
constructPath :: Program -> ProgramPath Expr
constructPath program = _constructPath (listify $ stmt program)

-- Function that will transform a statement into a ProgramPath
_constructPath :: PathStatements -> ProgramPath Expr
_constructPath ((IfThenElse expr ifStmt elseStmt) : stmts) = BranchPath (LitB True) Nothing (injectExpression expr ifPath) (injectExpression (OpNeg expr) elsePath)
  where
    ifPath = _constructPath $ listify ifStmt ++ stmts
    elsePath = _constructPath $ listify elseStmt ++ stmts
_constructPath ((While expr stmt) : stmts) = tree
  where
    tree = BranchPath (LitB True) Nothing skipWhile runs
    stmtTree = _constructPath $ listify stmt -- Construct a path of the inner statement. This is required because there may be nested special environments.
    skipWhile = injectExpression (OpNeg expr) (_constructPath stmts)
    runs = combinePaths stmtTree (BranchPath expr Nothing skipWhile runs) -- Construct paths for when the while runs
_constructPath (Assert invar : w@(While expr stmt) : stmts) = tree -- A loop with an invariant was found
  where
    tree = BranchPath (LitB True) Nothing whilePath InvalidPath
    -- Unroll everything in the while block, needed if there are special instructions (if-then-else, nested while) inside of this wile
    whilePath = AnnotedWhilePath invar expr (_constructPath $ listify stmt) (_constructPath stmts)
_constructPath (TryCatch eName tryStmts catchStmts : stmts) = tree
  where
    try = TryCatchPath (_constructPath $ listify tryStmts) eName (_constructPath $ listify catchStmts) (_constructPath stmts)
    excZero = BinopExpr Equal (Var "exc") (LitI 0)
    tryTree = BranchPath excZero Nothing try InvalidPath
    tree = BranchPath (LitB True) Nothing tryTree (EmptyPath (OpNeg excZero))
_constructPath ((Block vars stmt) : stmts) = error $ "Found unfiltered block! \r\n" ++ show stmt -- Block should be filtered out during splitList
_constructPath (stmt : stmts) = combinePaths (LinearPath (LitB True) stmt) $ _constructPath stmts
_constructPath [] = EmptyPath (LitB True)

-- Construct paths that will be evaluated when exc is not 0.
-- They can be used to find what kind of error was produced, as they explicitly set the corresponding exception code.
-- Note that they add an Assert False, thus they don't further evaluate the noErrorPath and are a form of early stopping when there is an exception.
errorCheckingPath :: ProgramPath Expr -> ProgramPath Expr
errorCheckingPath noErrorPath = BranchPath (LitB True) Nothing (injectExpression testNoException noErrorPath) t1
  where
    assignPath x = LinearPath (BinopExpr Equal (Var "exc") (LitI x)) (Assign "exc" (LitI x))
    unknownException = LinearPath (LitB True) (Assign "exc" (LitI (-1))) -- This path will only be taken if exc is not 0, and not one of the already defined numbers
    testNoException = BinopExpr Equal (Var "exc") (LitI 0)
    t1 = BranchPath (OpNeg testNoException) Nothing (assignPath 1) t2
    t2 = BranchPath (LitB True) Nothing (assignPath 2) t3
    t3 = BranchPath (LitB True) Nothing (assignPath 3) unknownException

-- Turns seq into a list of statements
unrollSeq :: Stmt -> PathStatements
unrollSeq (Seq s1 s2) = unrollSeq s1 ++ unrollSeq s2
unrollSeq s = [s]

-- Turns statement into list of statements that are either: while, if, vardecl, pure seq, single statement
listify :: Stmt -> PathStatements
listify allStmts = splitList (unrollSeq allStmts)

-- Turns a list of statements into a list of statements that are either: while, if, vardecl, pure seq, single statement
splitList :: PathStatements -> PathStatements
splitList allStmts = splitList' allStmts []

-- Turns a list of statements into a list of statements that are either: while, if, vardecl, pure seq, single statement
-- First parameter is list of single statements, second parameter is accumulator: list of pure single statements that can finally be put into a list
-- When the first non-pure statement is found, the accumulator will be rolled into a seq, added to the result list, then the unpure statement will be put in the list, then it will evaluate the other statements
splitList' :: PathStatements -> PathStatements -> PathStatements
splitList' [] [] = []
splitList' [] stmts = rollSeqr stmts
splitList' (w@While {} : statements) stmts = rollSeqr stmts ++ (w : splitList statements)
splitList' (t@TryCatch {} : statements) stmts = rollSeqr stmts ++ (t : splitList statements)
splitList' (Assert e : w@While {} : statements) stmts = rollSeqr stmts ++ [Assert e] ++ (w : splitList statements) -- Loop invariant found
splitList' (i@IfThenElse {} : statements) stmts = rollSeqr stmts ++ (i : splitList statements)
splitList' ((Block _ stmt) : statements) stmts = splitList' (listify stmt ++ statements) stmts -- Take code out of the block, and process as its own entity
splitList' (s : statements) stmts = splitList' statements (s : stmts)

-- Rolls a list of statements into a Seq, where the begin of the Seq is on the right of the list
rollSeqr :: PathStatements -> PathStatements
rollSeqr [] = []
rollSeqr stmts = [rollSeql $ reverse stmts]

-- Rolls a list of statements into a Seq, where the begin of the Seq is on the left of the list
rollSeql :: PathStatements -> Stmt
rollSeql [s] = s
rollSeql (s : ss) = Seq s (rollSeql ss)
rollSeql [] = error "Cannot roll empty array"

-- Injects the given expression into the condition for the given path
injectExpression :: Condition -> ProgramPath Expr -> ProgramPath Expr
injectExpression expr (LinearPath cond stmts) = LinearPath (BinopExpr And cond expr) stmts
injectExpression expr (BranchPath cond stmts option1 option2) = BranchPath (BinopExpr And cond expr) stmts option1 option2
injectExpression expr (EmptyPath cond) = EmptyPath (BinopExpr And cond expr)
injectExpression _ AnnotedWhilePath {} = error "Cannot inject expression into while block"
injectExpression _ TryCatchPath {} = error "Cannot inject expression into try-catch block"
injectExpression _ InvalidPath = InvalidPath

-- Utility function that can combine two ProgramPaths into a single ProgramPath
combinePaths :: ProgramPath Expr -> ProgramPath Expr -> ProgramPath Expr
combinePaths (LinearPath condA stmtA) (LinearPath condB stmtB) = LinearPath (simplifyExpr (BinopExpr And condA condB)) (Seq stmtA stmtB)
combinePaths (LinearPath condA lin) (BranchPath condB tStmts option1 option2) = BranchPath (simplifyExpr (BinopExpr And condA condB)) newStmts option1 option2 where newStmts = maybe (Just lin) (Just . Seq lin) tStmts
combinePaths (BranchPath cond tStmts option1 option2) linpath@LinearPath {} = BranchPath cond tStmts (combinePaths option1 linpath) (combinePaths option2 linpath)
combinePaths (BranchPath cond tStmts option1 option2) treepath@BranchPath {} = BranchPath cond tStmts (combinePaths option1 treepath) (combinePaths option2 treepath)
combinePaths (AnnotedWhilePath invar guard whilePath nextPath) otherPath = AnnotedWhilePath invar guard whilePath (combinePaths nextPath otherPath)
combinePaths (EmptyPath cond) otherPath = injectExpression cond otherPath
combinePaths otherPath empty@(EmptyPath cond) = combinePaths empty otherPath
combinePaths (TryCatchPath tryPath eName catchPath nextPath) otherPath = TryCatchPath tryPath eName catchPath (combinePaths nextPath otherPath)
combinePaths _ _ = InvalidPath

--
-- SECTION 2
--
-- The following functions are for finding and removing invalid paths, and
-- turning the tree to a tree of finite length.
--

--Wrapper for actual function, so it wont keep evaluating the infinite structure
removePaths :: Int -> ProgramPath Expr -> (ProgramPath Expr, RemainingPathCount)
removePaths depth tree
  | depth <= 0 = (InvalidPath, 0)
  | otherwise = _removePaths tree depth

_removePaths :: ProgramPath Expr -> Int -> (ProgramPath Expr, RemainingPathCount)
_removePaths (BranchPath _ _ InvalidPath InvalidPath) depth = (InvalidPath, 0) -- Prune a branch if both branches are invalid
_removePaths (BranchPath cond tStmts pathA pathB) depth
  | remDepth < 0 = (InvalidPath, 0) -- In this case all preceding statements are longer than what happens after branching, so K is exceeded anyway
  | otherwise = pruneInvalidBranch (BranchPath cond tStmts newA newB) -- Evaluate both paths. If both turn out to be unfeasible this node is pruned as well
  where
    baseDepth = splitDepth tStmts depth -- How many statements happen before the branch
    remDepth = depth - baseDepth -- The depth remaining after the preceding statements
    (newA, newACount) = removePaths remDepth pathA -- Evaluate path A, see if it is feasible given the depth
    (newB, newBCount) = removePaths remDepth pathB -- Evaluate path B, see if it is feasible given the depth
    pruneInvalidBranch (BranchPath cond _ InvalidPath InvalidPath) = (InvalidPath, 0) -- Invalidate path if both branches are unfeasible
    --
    pruneInvalidBranch tree@(BranchPath _ _ _ InvalidPath) = (tree, newACount)
    pruneInvalidBranch tree@(BranchPath _ _ InvalidPath _) = (tree, newBCount)
    pruneInvalidBranch tree = (tree, newACount + newBCount)
_removePaths (AnnotedWhilePath invar guard whilePath postPath) depth = pruneInvalidWhile (AnnotedWhilePath invar guard newA newB) -- Evaluate both paths. If any turn out to be unfeasible this node is pruned as well
  where
    (newA, newACount) = removePaths (depth - bDepth) whilePath -- Evaluate path A, see if it is feasible given the depth
    (newB, newBCount) = removePaths depth postPath -- Evaluate path B, see if it is feasible given the depth
    bDepth = totalDepth newB depth
    pruneInvalidWhile (AnnotedWhilePath _ _ InvalidPath _) = (InvalidPath, 0)
    pruneInvalidWhile (AnnotedWhilePath _ _ _ InvalidPath) = (InvalidPath, 0)
    --
    pruneInvalidWhile while = (while, newACount * newBCount)
_removePaths (TryCatchPath tryPath excName catchPath nextPath) depth = pruneInvalidTry (TryCatchPath newA excName newB newC) -- Evaluate both paths. If any turn out to be unfeasible this node is pruned as well
  where
    (newA, newACount) = removePaths depth tryPath -- Evaluate path A, see if it is feasible given the depth
    (newB, newBCount) = removePaths depth catchPath -- Evaluate path B, see if it is feasible given the depth
    (newC, newCCount) = removePaths depth nextPath -- Evaluate everything after this block, see if it is feasible given the depth
    pruneInvalidTry (TryCatchPath InvalidPath _ _ _) = (InvalidPath, 0)
    pruneInvalidTry (TryCatchPath _ _ InvalidPath _) = (InvalidPath, 0)
    pruneInvalidTry (TryCatchPath _ _ _ InvalidPath) = (InvalidPath, 0)
    --
    pruneInvalidTry try = (try, newACount * newBCount * newCCount)
_removePaths linpath@LinearPath {} depth
  | depth < totalDepth linpath depth = (InvalidPath, 0) -- Make path unfeasible if it exceeds the depth
  | otherwise = (linpath, 1)
_removePaths InvalidPath _ = (InvalidPath, 0)
_removePaths (EmptyPath _) _ = (InvalidPath, 0) -- Invalidate empty paths

--
-- SECTION 4
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
__printTree (AnnotedWhilePath invar guard option1 option2) depth k =
  tabs
    ++ "INVAR "
    ++ show invar
    ++ " WHILE "
    ++ show guard
    ++ " { "
    ++ "\n"
    ++ tabs
    ++ _printTree option1 remDepth k
    ++ "\n"
    ++ tabs
    ++ "}"
    ++ _printTree option2 depth k
  where
    baseDepth = totalDepth option2 depth
    remDepth = depth - baseDepth
    tabs = replicate (2 * (k - depth)) ' ' -- Tabs for same level
__printTree (TryCatchPath tryPath e catchPath nextPath) depth k =
  tabs
    ++ "TRY {\n"
    ++ tabs
    ++ _printTree tryPath remDepth' k
    ++ "\n"
    ++ tabs
    ++ "}"
    ++ "\n"
    ++ "CATCH "
    ++ show e
    ++ "{ \n"
    ++ tabs
    ++ _printTree catchPath remDepth k
    ++ "\n"
    ++ tabs
    ++ "}"
    ++ _printTree nextPath depth k
  where
    baseDepth = totalDepth nextPath depth
    baseDepth' = totalDepth catchPath baseDepth
    remDepth = depth - baseDepth
    remDepth' = depth - baseDepth - baseDepth'
    tabs = replicate (2 * (k - depth)) ' ' -- Tabs for same level
__printTree (BranchPath cond tStmts option1 option2) depth k =
  tabs
    ++ "[ "
    ++ show cond
    ++ "]\n"
    ++ tabs
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
    depth2 = totalDepth option2 (depth - depth3) -- Length of catch statements
    depth1 = totalDepth option1 (depth - depth3 - depth2) -- Length of try statements
_totalDepth linpath@LinearPath {} depth = totalDepth linpath depth -- If this function was called directly, this will send a linear path back to the wrapper

-- Utility function that can check the depth of a Maybe Stmt (0 if none is present, n if there is a Stmt)
splitDepth :: Maybe Stmt -> Int -> Int
splitDepth tStmts depth = maybe 0 countStatements tStmts
