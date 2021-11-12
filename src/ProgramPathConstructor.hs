module ProgramPathConstructor where

import Data.Maybe (fromMaybe)
import ExpressionOps (simplifyExpr)
import GCLParser.GCLDatatype (BinOp (..), Expr (..), Program (..), Stmt (..))
import GeneralTypes (Condition, PathStatements)
import ProgramPath
import ProgramPathOps (splitDepth, totalDepth)
import StatementOps (listify)

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
    (newB, newBCount) = removePaths depthAfterTry catchPath -- Evaluate path B, see if it is feasible given the depth
    (newC, newCCount) = removePaths depthAfterCatch nextPath -- Evaluate everything after this block, see if it is feasible given the depth
    maxDepthTry = totalDepth tryPath depth -- See how deep try path goes, if there isn't a loop or block in there it cannot be too far
    depthAfterTry = if maxDepthTry < depth then depth - maxDepthTry else depth
    maxDepthCatch = totalDepth catchPath depthAfterTry -- See how deep catch path goes, if there isn't a loop or block in there it cannot be too far
    depthAfterCatch = if maxDepthCatch < depthAfterTry then depthAfterTry - maxDepthCatch else depthAfterTry

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
