module ProgramPath where

import Data.Map (Map, empty, filter, insert, intersection, toList)
import qualified Data.Map (map)
import Data.Maybe (catMaybes, fromMaybe)
import GCLParser.GCLDatatype
import WLP (considerExpr, convertVarMap, evalExpr, simplifyExpr, wlp)
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

--Function that will transform a statement into a ProgramPath
_constructPath :: Stmt -> ProgramPath Expr
_constructPath (IfThenElse expr ifStmt elseStmt) = TreePath (LitB True) Nothing (injectExpression expr ifPath) (injectExpression (OpNeg expr) elsePath)
  where
    ifPath = _constructPath ifStmt
    elsePath = _constructPath elseStmt
_constructPath (While expr stmt) = TreePath (LitB True) Nothing (EmptyPath (OpNeg expr)) runs
  where
    stmtTree = _constructPath stmt --Construct a path of the inner statement. This is required because there may be nested special environments.
    runs = combinePaths stmtTree (TreePath expr Nothing runOnce runMore) --Construct paths for when the while runs
    runOnce = EmptyPath (OpNeg expr)
    runMore = _constructPath (While expr stmt)
_constructPath (Seq stmt nextStmt) = combinePaths s1 s2
  where
    s1 = _constructPath stmt
    s2 = _constructPath nextStmt
_constructPath (Block vars stmt) = _constructPath stmt --TODO This may miss out on some variables! Needs checking
_constructPath stmt = LinearPath (LitB True) stmt

--Injects the given expression into the condition for the given path
injectExpression :: Expr -> ProgramPath Expr -> ProgramPath Expr
injectExpression expr (LinearPath cond stmts) = LinearPath (BinopExpr And cond expr) stmts
injectExpression expr (TreePath cond stmts option1 option2) = TreePath (BinopExpr And cond expr) stmts option1 option2
injectExpression expr (EmptyPath cond) = EmptyPath (BinopExpr And cond expr)
injectExpression _ InvalidPath = InvalidPath

--Utility function that can combine two ProgramPaths into a single ProgramPath
combinePaths :: ProgramPath Expr -> ProgramPath Expr -> ProgramPath Expr
combinePaths (LinearPath condA stmtA) (LinearPath condB stmtB) = LinearPath (simplifyExpr (BinopExpr And condA condB)) (combineStatements stmtA stmtB)
combinePaths (LinearPath condA lin) (TreePath condB tStmts option1 option2) = TreePath (simplifyExpr (BinopExpr And condA condB)) newStmts option1 option2 where newStmts = maybe (Just lin) (Just . combineStatements lin) tStmts
combinePaths (TreePath cond tStmts option1 option2) linpath@LinearPath {} = TreePath cond tStmts (combinePaths option1 linpath) (combinePaths option2 linpath)
combinePaths (TreePath cond tStmts option1 option2) treepath@TreePath {} = TreePath cond tStmts (combinePaths option1 treepath) (combinePaths option2 treepath)
combinePaths (EmptyPath cond) otherPath = injectExpression cond otherPath
combinePaths otherPath empty@(EmptyPath cond) = combinePaths empty otherPath
combinePaths _ _ = InvalidPath

combineStatements (Seq a b) c = Seq a (combineStatements b c)
combineStatements s1 s2 = Seq s1 s2

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
  | otherwise = pruneInvalidBranch (TreePath cond tStmts newA newB) --Evaluate both paths. If both turn out to be unfeasible this node is pruned as well
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

--Returns the number of nodes with a condition of false for a path of FIXED LENGTH
numConditionFalse :: Num p => ProgramPath Expr -> p
numConditionFalse = foldTreeCond conditionCheck 0 id
  where
    conditionCheck (LitB False) prev = 1 + prev
    conditionCheck _ prev = prev

-- Note that this function assumes that all ifs and whiles have been removed from the path
countStatements :: Num p => Stmt -> p
countStatements (Seq a b) = countStatements a + countStatements b
countStatements (Block _ stmts) = countStatements stmts
countStatements _ = 1

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
    ++ _printTree option2 remDepth (k + 1) --Add k+1, because Nothing as tStmts may lead to it thinking it is on the same level
  where
    baseDepth = splitDepth tStmts depth
    remDepth = depth - baseDepth
    tabs = replicate (2 * (k - depth)) ' ' --Tabs for same level

--Get the length of the longest branched path
--Wrapper for actual function, so it wont keep evaluating the infinite structure
--Note that linear paths should be allowed to be evaluated further than depth, as otherwise we won't know if they are too long. If they are too long however the returned value will be > the given depth, so it can be derived that this path is too long
totalDepth :: ProgramPath a -> Int -> Int
totalDepth (LinearPath _ stmts) depth = countStatements stmts --Depth of a linear path is just counting the statements statement
totalDepth path depth --Wrapper for handling of non-linear ProgramPath structure
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
splitDepth tStmts depth = maybe 0 countStatements tStmts

--
-- SECTION 5
--
-- The following functions are to transform the tree into a Z3 structure and to evaluate that structure
--

evaluateFullTree :: ProgramPath Expr -> [(Map String Expr -> Expr, ProgramPath Expr)]
evaluateFullTree (TreePath cond stmts option1 option2) = do
  let expr1 = evaluateFullTree option1
  let expr2 = evaluateFullTree option2
  -- Calculates the wlp over branch node statements
  -- If it has statements, runs wlp using the precondition of expr1, else just returns that precondition
  let wlps1 = map concatPaths expr1
  let wlps2 = map concatPaths expr2
  wlps1 ++ wlps2
  where
    myPath = maybe (EmptyPath cond) (LinearPath cond) stmts
    addCond wlp = \v -> simplifyExpr (BinopExpr Implication (considerExpr cond v) (wlp v))
    concatPaths (expr, path) = (addCond (maybe expr (`wlp` expr) stmts), combinePaths myPath path)
evaluateFullTree linpath@(LinearPath cond stmts) = do
  let path = wlp stmts (\v -> LitB True)
  let condExpr = considerExpr cond
  [(\vars -> simplifyExpr (BinopExpr Implication (condExpr vars) (path vars)), linpath)]
evaluateFullTree (EmptyPath cond) = [(const cond, EmptyPath cond)]
evaluateFullTree InvalidPath = [(const (LitB False), InvalidPath)]

-- Calculates the WLP over a program path
calcWLP :: ProgramPath Expr -> Map String Expr -> [(Expr, ProgramPath Expr)]
calcWLP tree vars = do
  let wlpsAndTrees = evaluateFullTree tree
  map (\(expr, path) -> (simplifyExpr (expr vars), path)) wlpsAndTrees

-- Outputs if an expression can be contradicted. If so, also outputs how
verifyExpr :: Expr -> (Map String Expr, Map String Type) -> IO Result
verifyExpr expr (vars, types) =
  evalZ3 script >>= \(result, sol) ->
    case result of
      Sat -> do
        putStrLn "Found a counter example: "
          >> putStrLn "Integers, Bools, Arrays"
          >> putStrLn (show (map fst (toList intNames)) ++ show (map fst (toList boolNames)) ++ show (map fst (toList arrayNames)))
          >> putStrLn sol
        return result
      _ -> return result
  where
    z3vars = convertVarMap (vars, types)
    intNames = Data.Map.filter onlyInts types
    boolNames = Data.Map.filter onlyBools types
    arrayNames = Data.Map.filter onlyArrays types
    script = do
      reset
      push
      assert =<< evalExpr expr z3vars
      newVars <- mapM snd (toList z3Ints)
      (_, intMaybe) <- withModel $ \m ->
        catMaybes <$> mapM (evalInt m) newVars

      newVars <- mapM snd (toList z3Arrays)
      (_, arrayMaybe) <- withModel $ \m ->
        map interpMap <$> (catMaybes <$> mapM (evalArray m) newVars)

      newVars <- mapM snd (toList z3Bools)
      (result, boolMaybe) <- withModel $ \m ->
        catMaybes <$> mapM (evalBool m) newVars
      let display = unMaybe intMaybe ++ unMaybe boolMaybe ++ unMaybe arrayMaybe
      return (result, display)

    z3Ints = intersection z3vars intNames
    z3Bools = intersection z3vars boolNames
    z3Arrays = intersection z3vars arrayNames
    onlyInts (PType PTInt) = True
    onlyInts _ = False
    onlyBools (PType PTBool) = True
    onlyBools _ = False
    onlyArrays (AType _) = True
    onlyArrays _ = False
    unMaybe m = maybe "" show m

-- Turns a given expression into an AST
z3Script :: MonadZ3 z3 => Expr -> (Map String Expr, Map String Type) -> z3 AST
z3Script expr (vars, types) = evalExpr expr z3vars
  where
    z3vars = convertVarMap (vars, types)

-- Returns the names of variables that are not set to a primitive value
mutatedVariables :: Map String Expr -> [String]
mutatedVariables vars = z3Environment
  where
    convert (key, Var name)
      | key == name = [name]
      | otherwise = []
    convert (key, expr) = []
    z3Environment = concatMap convert (toList vars)

addExprVariable :: (Map String Expr, Map String Type) -> VarDeclaration -> (Map String Expr, Map String Type)
addExprVariable (map, ts) (VarDeclaration name t@(PType _)) = (insert name (Var name) map, insert name t ts)
addExprVariable (map, ts) (VarDeclaration name t@(AType _)) = (insert name (Var name) (insert ("#" ++ name) (Var ("#" ++ name)) map), insert name t (insert ("#" ++ name) (PType PTInt) ts))
addExprVariable _ (VarDeclaration _ t) = error $ "This program does not support variables of type " ++ show t
