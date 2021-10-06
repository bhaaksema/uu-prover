module ProgramPath where

import Data.Maybe (fromMaybe)
import GCLParser.GCLDatatype
import GCLParser.Parser (ParseResult, parseGCLfile)
import WLP (evalExpr, evalStmt)
import Z3.Monad

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
  | EmptyPath a --Path that does not yet contain any statements or branches
  | InvalidPath -- Either because branch condition was unfeasible or because depth was too deep
  deriving (Show)

--
-- SECTION 1
--
-- The following functions are to build the path
--

--Function that will transform a Program into a ProgramPath
constructPath :: Program -> ProgramPath Expr
constructPath program = _constructPath (stmt program)

--Function that will transform a statement into a Programpath
_constructPath :: Stmt -> ProgramPath Expr
_constructPath (IfThenElse expr ifStmt elseStmt) = TreePath (LitB True) Nothing (injectExpression expr (_constructPath ifStmt)) (injectExpression (OpNeg expr) (_constructPath elseStmt))
_constructPath (While expr stmt) = TreePath (LitB True) Nothing (EmptyPath expr) runs
  where
    runs = TreePath (LitB True) Nothing runOnce runMore --Construct paths for when the while runs
    runOnce = injectExpression expr (_constructPath stmt)
    runMore = combinePaths runOnce (_constructPath (Seq stmt (While expr stmt)))
_constructPath (Seq stmt nextStmt) = combinePaths (_constructPath stmt) (_constructPath nextStmt)
_constructPath stmt = LinearPath (LitB True) stmt

--Injects the given expression into the condition for the given path
injectExpression :: Expr -> ProgramPath Expr -> ProgramPath Expr
injectExpression expr (LinearPath cond stmts) = LinearPath (BinopExpr And cond expr) stmts
injectExpression expr (TreePath cond stmts option1 option2) = TreePath (BinopExpr And cond expr) stmts option1 option2
injectExpression expr (EmptyPath cond) = EmptyPath (BinopExpr And cond expr)
injectExpression _ InvalidPath = InvalidPath

--Utility function that can combine two ProgramPaths into a single ProgramPath
combinePaths :: ProgramPath Expr -> ProgramPath Expr -> ProgramPath Expr
combinePaths (LinearPath condA stmtA) (LinearPath condB stmtB) = LinearPath (BinopExpr And condA condB) (Seq stmtA stmtB)
combinePaths (LinearPath condA lin) (TreePath condB tStmts option1 option2) = TreePath (BinopExpr And condA condB) newStmts option1 option2 where newStmts = maybe (Just lin) (Just . Seq lin) tStmts
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
removePaths :: ProgramPath Expr -> Int -> ProgramPath Expr
removePaths tree depth
  | depth <= 0 = InvalidPath
  | otherwise = _removePaths tree depth

_removePaths :: ProgramPath Expr -> Int -> ProgramPath Expr
_removePaths (TreePath _ _ InvalidPath InvalidPath) depth = InvalidPath --Prune a branch if both branches are invalid
_removePaths (TreePath cond tStmts pathA pathB) depth
  | remDepth < 0 = InvalidPath --In this case all preceding statements are longer than what happens after branching, so K is exceeded anyway
  | otherwise = pruneInvalidBranch (TreePath cond tStmts newA newB) --Evaluate boths paths. If both turn out to be unfeasable this node is pruned as well
  where
    baseDepth = splitDepth tStmts depth --How many statements happen before the branch
    remDepth = depth - baseDepth --The depth remaining after the preceding statements
    newA = removePaths pathA remDepth --Evaluate path A, see if it is feasible given the depth
    newB = removePaths pathB remDepth --Evaluate path B, see if it is feasible given the depth
    pruneInvalidBranch (TreePath cond _ InvalidPath InvalidPath) = InvalidPath --Invalidate path if both branches are unfeasible
    --
    pruneInvalidBranch (TreePath condA (Just tStmts) InvalidPath (LinearPath condB stmt)) = LinearPath (BinopExpr And condA condB) (Seq tStmts stmt) --Linearise a branch if only one of the paths is feasible
    pruneInvalidBranch (TreePath condA Nothing InvalidPath (LinearPath condB stmt)) = LinearPath (BinopExpr And condA condB) stmt --Linearise a branch if only one of the paths is feasible
    pruneInvalidBranch (TreePath condA tStmts linpath@LinearPath {} InvalidPath) = pruneInvalidBranch (TreePath condA tStmts InvalidPath linpath) --Swap arguments and run previous case
    --
    pruneInvalidBranch (TreePath condA (Just tStmts) InvalidPath (TreePath condB (Just stmt) option1 option2)) = TreePath (BinopExpr And condA condB) (Just (Seq tStmts stmt)) option1 option2 --Combine branches to one big branch
    pruneInvalidBranch (TreePath condA (Just tStmts) InvalidPath (TreePath condB Nothing option1 option2)) = TreePath (BinopExpr And condA condB) (Just tStmts) option1 option2 --Combine branches to one big branch
    pruneInvalidBranch (TreePath condA Nothing InvalidPath (TreePath condB stmts option1 option2)) = TreePath (BinopExpr And condA condB) stmts option1 option2 --Combine branches to one big branch
    pruneInvalidBranch (TreePath condA tStmts treepath@TreePath {} InvalidPath) = pruneInvalidBranch (TreePath condA tStmts InvalidPath treepath) --Swap arguments and run previous case
    --
    pruneInvalidBranch tree = tree
_removePaths linpath@LinearPath {} depth
  | depth < totalDepth linpath depth = InvalidPath --Make path unfeasible if it exceeds the depth
  | otherwise = linpath
_removePaths InvalidPath _ = InvalidPath
_removePaths (EmptyPath _) _ = InvalidPath --Invalidate empty paths

--Wrapper for actual function, so it wont keep evaluating the infinite structure
flagInvalid :: ProgramPath Expr -> Int -> ProgramPath Expr
flagInvalid tree depth
  | depth <= 0 = InvalidPath
  | otherwise = _flagInvalid tree depth

_flagInvalid :: ProgramPath Expr -> Int -> ProgramPath Expr
_flagInvalid (TreePath cond tStmts pathA pathB) depth
  | remDepth < 0 = InvalidPath --Invalidate branch node if its statements are longer than the allowed depth
  | otherwise = TreePath cond tStmts (flagInvalid pathA remDepth) (flagInvalid pathB remDepth)
  where
    baseDepth = splitDepth tStmts depth --How many statements happen before the branch
    remDepth = depth - baseDepth --The depth remaining after the preceding statements
_flagInvalid linpath@LinearPath {} depth
  | depth < totalDepth linpath depth = InvalidPath --Make path unfeasible if it exceeds the depth
  | otherwise = linpath
_flagInvalid InvalidPath _ = InvalidPath
_flagInvalid (EmptyPath _) _ = InvalidPath --Invalidate empty paths

--
-- SECTION 3
--
-- These function define basic operations over the tree structure.
-- These functions are map and fold
--

--Folds the tree on the condition field
foldTreeCond :: (cond -> result -> result) -> result -> (result -> result) -> ProgramPath cond -> result
foldTreeCond _ init invalid InvalidPath = invalid init
foldTreeCond condFunc initial _ (EmptyPath cond) = condFunc cond initial
foldTreeCond condFunc initial _ (LinearPath cond _) = condFunc cond initial
foldTreeCond f init inv (TreePath cond _ option1 option2) = fold
  where
    fold = foldTreeCond f middle inv option2
    middle = f cond first
    first = foldTreeCond f init inv option1

--Folds the tree on the statement field
foldTreeStmt :: (Stmt -> result -> result) -> result -> (result -> result) -> ProgramPath a -> result
foldTreeStmt _ init invalid InvalidPath = invalid init
foldTreeStmt stmtFunc init invalid (EmptyPath _) = invalid init
foldTreeStmt stmtFunc initial _ (LinearPath _ stmt) = stmtFunc stmt initial
foldTreeStmt f init inv (TreePath _ stmt option1 option2) = fullfold
  where
    fullfold = foldTreeStmt f middle inv option2
    middle = fromMaybe first middleFolded --If stmt was Nothing, this returns first, else it returns foldTree over stmt with initial value first
    middleFolded = (`f` first) <$> stmt
    first = foldTreeStmt f init inv option1

mapTree :: (t -> a) -> (Stmt -> Stmt) -> ProgramPath t -> ProgramPath a
mapTree _ _ InvalidPath = InvalidPath
mapTree condFunc _ (EmptyPath cond) = EmptyPath (condFunc cond)
mapTree condFunc stmtFunc (LinearPath cond stmt) = LinearPath (condFunc cond) (stmtFunc stmt)
mapTree condFunc stmtFunc (TreePath cond stmt option1 option2) = TreePath (condFunc cond) (stmtFunc <$> stmt) (mapTree' option1) (mapTree' option2)
  where
    mapTree' = mapTree condFunc stmtFunc

--
-- SECTION 4
--
-- The following functions are used to calculate properties over, and print information about the tree
--

countBranches :: Num p => ProgramPath a -> p
countBranches (TreePath _ _ option1 option2) = countBranches option1 + countBranches option2 + 1
countBranches _ = 0

--Returns the number of invalid nodes for a path of FIXED LENGTH
numInvalid :: Num p => ProgramPath a -> p
numInvalid = foldTreeStmt (\_ prev -> prev) 0 (+ 1)

--Print the whole tree for the given program path
--Wrapper for actual function, so it wont keep evaluating the infinite structure
printTree :: Show a => ProgramPath a -> Int -> String
printTree tree depth = _printTree tree depth depth

_printTree :: Show a => ProgramPath a -> Int -> Int -> String
_printTree tree depth k
  | depth < 0 = "Depth exceeded"
  | otherwise = __printTree tree depth k

__printTree :: Show a => ProgramPath a -> Int -> Int -> String
__printTree InvalidPath _ _ = "INVALID PATH FOUND"
__printTree (EmptyPath _) _ _ = "LOOSE EMPTY PATH FOUND"
__printTree (LinearPath cond (Seq a b)) depth k = _printTree (LinearPath cond a) depth k ++ _printTree (LinearPath cond b) remDepth k
  where
    aDepth = totalDepth (LinearPath cond a) depth
    remDepth = depth - aDepth
__printTree (LinearPath cond stmt) _ _ = show stmt
__printTree (TreePath cond tStmts option1 option2) depth k = tabs ++ show tStmts ++ "\n" ++ tabs ++ "Branch1:\n" ++ tabs ++ _printTree option1 remDepth (k + 1) ++ "\n" ++ tabs ++ "Branch2:\n" ++ _printTree option2 remDepth (k + 1) --Add k+1, because Nothing as tStmts may lead to it thinking it is on the same level
  where
    baseDepth = splitDepth tStmts depth
    remDepth = depth - baseDepth
    tabs = replicate (k - depth) '\t' --Tabs for same level

--Get the length of the longest branched path
--Wrapper for actual function, so it wont keep evaluating the infinite structure
--Note that linear paths should be allowed to be evaluated further than depth, as otherwise we won't know if they are too long. If they are too long however the returned value will be > the given depth, so it can be derived that this path is too long
totalDepth :: ProgramPath a -> Int -> Int
totalDepth (LinearPath cond (Seq a b)) depth = aDepth + totalDepth (LinearPath cond b) remDepth --The length of a Seq is the length of the first statement + length of the second statement (where second statement should not be evaluated further than depth - length of first statement)
  where
    aDepth = totalDepth (LinearPath cond a) depth --Length of the first statement
    remDepth = depth - aDepth --Length remaining for the second statement
totalDepth (LinearPath _ _) depth = 1 --Depth of a single statement
totalDepth path depth --Wrapper for handeling of non-linear ProgramPath structure
  | depth <= 0 = depth --Cut off when max depth was reached
  | otherwise = _totalDepth path depth

_totalDepth :: ProgramPath a -> Int -> Int
_totalDepth InvalidPath depth = 0 --Invalid path has no depth
_totalDepth (EmptyPath _) depth = 0 --Empty path has no depth
_totalDepth (TreePath _ tStmts option1 option2) depth = baseDepth + max (totalDepth option1 remDepth) (totalDepth option2 remDepth) --Length of a branching path is length of preceding statements + max(length branch 1, length branch 2)
  where
    baseDepth = splitDepth tStmts depth --Length of preceding statements
    remDepth = depth - baseDepth --Depth remaining to explore after the preceding statements
_totalDepth linpath@LinearPath {} depth = totalDepth linpath depth --If this function was called directly, this will send a linear path back to the wrapper

--Utility function that can check the depth of a Maybe Stmt (0 if none is present, n if there is a Stmt)
splitDepth :: Maybe Stmt -> Int -> Int
splitDepth tStmts depth = maybe 0 (\s -> totalDepth (LinearPath (LitB True) s) depth) tStmts

--
-- SECTION 5
--
-- The following functions are to transform the tree into a Z3 structure and to evaluate that structure
--

--Transform conditions from Expr to Z3 AST
treeExprToZ3 :: ProgramPath Expr -> ProgramPath (Z3 AST)
treeExprToZ3 = mapTree evalExpr id

evaluateFullTree :: MonadZ3 z3 => ProgramPath (z3 AST) -> z3 AST
evaluateFullTree (TreePath cond stmts option1 option2) = do
  z3Stmts <- maybe mkTrue evalStmt stmts
  z31 <- evaluateFullTree option1
  z32 <- evaluateFullTree option2
  z3cond <- cond
  and <- mkAnd [z3Stmts, z31, z32]
  mkImplies z3cond and
evaluateFullTree (LinearPath cond stmts) = do
  z3cond <- cond
  z3Stmts <- evalStmt stmts
  mkImplies z3cond z3Stmts
evaluateFullTree (EmptyPath cond) = cond
evaluateFullTree InvalidPath = mkFalse

verifyTree :: ProgramPath (Z3 AST) -> IO Result
verifyTree tree = evalZ3 $ do
  assert =<< evaluateFullTree tree
  check

--
-- SECTION 6
--
-- The following functions will run the 'main' program and output the required informations
--

-- main loads the file and puts the ParseResult Program through the following functions
run = do
  program <- parseGCLfile "test/input/min.gcl"
  let k = 10
  evaluateProgram program k

evaluateProgram (Left _) k = putStrLn "Unable to parse program"
evaluateProgram (Right program) k = do
  let path = constructPath program
  let flaggedPath = flagInvalid path k

  let pathsTooLong = numInvalid flaggedPath
  putStrLn ("Results when using k=" ++ show k ++ " on the specified program:")
  putStrLn []
  putStrLn ("Found a total of " ++ show (countBranches flaggedPath) ++ " possible program paths.")
  putStrLn ("Of these paths, at least " ++ show pathsTooLong ++ " are infeasible as they are too long.")
  putStrLn []

  putStrLn "Removing these infeasible paths..."
  putStrLn []
  let clearedPath = removePaths path k
  putStrLn ("Reduced structure to " ++ show (countBranches clearedPath) ++ " paths.")
  putStrLn "Evaluating this reduced structure gives:"
  putStrLn []
  --putStrLn (printTree clearedPath k)

  let z3Path = treeExprToZ3 clearedPath
  result <- verifyTree z3Path
  putStrLn "All paths satisfiable?"
  print result

--print path