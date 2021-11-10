{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Evaluator where

import Data.Map (Map, empty, filter, fromList, insert, intersection, keys, mapWithKey, toList, (!))
import Data.Maybe (catMaybes, fromMaybe)
import GCLParser.GCLDatatype
import ProgramPath (ProgramPath (..), combinePaths, unrollSeq)
import WLP (considerExpr, evalExpr, simplifyExpr, traceVarExpr, wlp)
import Z3.Monad

evaluateFullTree :: ProgramPath Expr -> (Map String Expr -> Expr) -> [(Map String Expr -> Expr, [Stmt])]
evaluateFullTree treepath@(TreePath cond stmts option1 option2) postCond
  | cond == LitB False = []
  | otherwise = do
    let expr1 = evaluateFullTree option1 postCond
    let expr2 = evaluateFullTree option2 postCond
    -- Calculates the wlp over branch node statements
    -- If it has statements, runs wlp using the precondition of expr1, else just returns that precondition
    let wlps1 = map concatPaths expr1
    let wlps2 = map concatPaths expr2
    wlps1 ++ wlps2
  where
    myPath = maybe [] unrollSeq stmts
    addCond wlp = \v -> simplifyExpr (BinopExpr Implication (considerExpr cond v) (wlp v))
    concatPaths (expr, path) = (addCond (maybe expr (`wlp` expr) stmts), myPath ++ path)
evaluateFullTree whilepath@(AnnotedWhilePath invar guard whilePath nextPath) postCond = do
  let wlpsOverS = evaluateFullTree whilePath (considerExpr invar)
  let qs = evaluateFullTree nextPath postCond

  -- Create all possible combinations of the inner while path and the next path.
  -- Note that all possible combinations need to be checked, as we don't know in advance whether there is an unannoted while within this while.
  -- Moreover other branching structures need to be evaluated as well (like if-then-else).
  let combos = [(setup whilePath wlpOverS q, whilePath ++ nextPath) | (wlpOverS, whilePath) <- wlpsOverS, (q, nextPath) <- qs]
  combos
  where
    setup whilePath wlpOverS q vars = do
      let newVars = freshenModifiedVars whilePath vars

      let wlpOverSEvaluated = wlpOverS newVars
      let iAndNotG = BinopExpr And invar (OpNeg guard)
      let iAndG = BinopExpr And invar guard
      let iNotGImpliesQ = BinopExpr Implication iAndNotG (q newVars)
      let iGImpliesWlp = BinopExpr Implication iAndG wlpOverSEvaluated

      -- An invariant is valid only if i /\ g => wlp S I AND i /\ ~g => Q AND i = True
      let evaluatedInvar = considerExpr invar vars
      let validInvar = considerExpr (BinopExpr And evaluatedInvar (BinopExpr And iNotGImpliesQ iGImpliesWlp)) newVars
      let triggerExc = q (insert "exc" (LitI 3) vars) -- Run rest of program, but with exception set to 3
      let invarIfValid = BinopExpr And (BinopExpr Implication validInvar evaluatedInvar) (BinopExpr Implication (OpNeg validInvar) triggerExc)
      invarIfValid

    -- This function goes through a list of statements and adds variables that are assigned to as a fresh variable a map of existing variables.
    -- This is used to evaluate the variables in i /\ g = wlp and i /\ ~g => Q as fresh variables, as is required to evaluate these expressions correctly.
    freshenModifiedVars [] vars = vars
    freshenModifiedVars (Assign name _ : stmts) vars = insert name (Var name) (freshenModifiedVars stmts vars)
    freshenModifiedVars (_ : stmts) vars = freshenModifiedVars stmts vars
evaluateFullTree linpath@(LinearPath cond stmts) postCond
  | cond == LitB False = []
  | otherwise = do
    let path = wlp stmts postCond -- Postcondition is: exception must be code 0 (no exception)
    let condExpr = considerExpr cond
    [(\vars -> simplifyExpr (BinopExpr Implication (condExpr vars) (path vars)), unrollSeq stmts)]
evaluateFullTree (EmptyPath cond) postCond = [(const cond, [])]
evaluateFullTree InvalidPath postCond = [] --Ignore invalid path

evaluateTreeConds :: ProgramPath Expr -> Map String Expr -> Map String (Z3 AST) -> IO (ProgramPath Expr)
evaluateTreeConds (TreePath cond stmts option1 option2) vars varmap = do
  let evaluatedCond = considerExpr cond vars
  condExpr <- z3Satisfiable evaluatedCond varmap
  let newVars = maybe vars (`traceVarExpr` vars) stmts
  case condExpr of
    LitB False -> return (TreePath condExpr stmts option1 option2)
    _ -> do
      newTree1 <- evaluateTreeConds option1 newVars varmap
      newTree2 <- evaluateTreeConds option2 newVars varmap
      return (TreePath condExpr stmts newTree1 newTree2)
evaluateTreeConds path@(AnnotedWhilePath invar guard whilePath nextPath) vars varmap = return path -- Note that no path can be evaluated anymore now! There could be many possibilities of variables changing inside of the whilePath if it has a tree inside it.
evaluateTreeConds linpath@(LinearPath cond stmts) vars varmap = do
  let evaluatedCond = considerExpr cond vars
  condExpr <- z3Satisfiable evaluatedCond varmap
  return $ LinearPath condExpr stmts
evaluateTreeConds (EmptyPath cond) vars varmap = do
  let evaluatedCond = considerExpr cond vars
  condExpr <- z3Satisfiable evaluatedCond varmap
  return $ EmptyPath condExpr
evaluateTreeConds InvalidPath _ _ = return InvalidPath

-- Calculates the WLP over a program path
calcWLP :: ProgramPath Expr -> Map String Expr -> [(Expr, [Stmt])]
calcWLP tree vars = do
  let wlpsAndTrees = evaluateFullTree tree (considerExpr (BinopExpr Equal (Var "exc") (LitI 0)))
  map (\(expr, path) -> (simplifyExpr (expr vars), path)) wlpsAndTrees

-- Outputs if an expression can be contradicted. If so, also outputs how
verifyExpr :: Expr -> (Map String (Z3 AST), Map String Type) -> IO Result
verifyExpr expr (z3vars, types) =
  evalZ3 script >>= \(result, intMaybe, boolMaybe, arrayMaybe) ->
    case result of
      Sat -> do
        let intValueMap = fromList $ zip (keys intNames) (fromMaybe [] intMaybe) -- Map of (name, Integer), allows us to get array lengths (using #name)
        let arrays = map (fromMaybe []) arrayMaybe -- Map the fromMaybe function over all the arrays. Should be safe as it is only nothing when there is no counter example
        let arraysWithNames = zip (map fst (toList arrayNames)) arrays -- Make a list of tuples, so that the name of each array is available (i.e. [(arrayname, array)])
        let arrayValues = map (\(name, array) -> getFirstN (intValueMap ! ("#" ++ name)) array) arraysWithNames -- Get the first #name elements of the infinite z3 array.
        putStrLn "counterexample found: "
          >> putStrLn "ints"
          >> print (map fst (toList intNames))
          >> putStrLn (unMaybe intMaybe)
          >> putStrLn []
          >> putStrLn "bools"
          >> print (map fst (toList boolNames))
          >> putStrLn (unMaybe boolMaybe)
          >> putStrLn []
          >> putStrLn "arrays"
          >> print (map fst (toList arrayNames))
          >> print arrayValues
          >> putStrLn []
        return result
      _ -> return result
  where
    -- Dictonaries of variable, type with only the given type
    intNames = Data.Map.filter (onlyPrimitive PTInt) types
    boolNames = Data.Map.filter (onlyPrimitive PTBool) types
    arrayNames = Data.Map.filter onlyArrays types

    -- Gets the first n elements from an array of integers
    getFirstN 0 _ = []
    getFirstN _ [] = []
    getFirstN n (x : xs :: [Integer]) = x : getFirstN (n - 1) xs

    -- Script to run to get a counter example
    script = do
      reset
      push
      assert =<< evalExpr expr z3vars
      newVars <- mapM snd (toList z3Ints)
      (_, intMaybe) <- withModel $ \m ->
        catMaybes <$> mapM (evalInt m) newVars

      let arrayNames = map fst (toList z3Arrays)
      arrayElements <- mapM (\name -> sequence (createArrayGetter name 0)) arrayNames
      arrayMaybe' <- mapM (\a -> withModel $ \m -> catMaybes <$> mapM (evalInt m) a) arrayElements
      let arrayMaybe = map snd arrayMaybe'

      newVars <- mapM snd (toList z3Bools)
      (result, boolMaybe) <- withModel $ \m ->
        catMaybes <$> mapM (evalBool m) newVars
      return (result, intMaybe, boolMaybe, arrayMaybe)

    -- Dicts of z3 variables that have only a specific type
    z3Ints = intersection z3vars intNames
    z3Bools = intersection z3vars boolNames
    z3Arrays = intersection z3vars arrayNames

    -- Filters to get variables of a specific type. Necessary because we need different eval functions for bools, arrays and ints.
    onlyPrimitive expectedType (PType ptype) = ptype == expectedType
    onlyPrimitive _ _ = False
    onlyArrays (AType _) = True
    onlyArrays _ = False

    unMaybe m = maybe "" show m -- Turn the maybe into a string

    -- Create an array of integer variables, so that all values can be extracted from array
    createArrayGetter arrayName 999 = []
    createArrayGetter arrayName i = do
      getArrayElem arrayName i : createArrayGetter arrayName (i + 1)

    -- Selects item with given index from the array with given name
    getArrayElem arrayName index = do
      array <- z3Arrays ! arrayName
      i <- mkInteger $ index - 1
      mkSelect array i

-- Checks an expression using a Z3 variable map. If it is not satisfiable will return the LitB expression, else the original expression.
z3Satisfiable :: Expr -> Map String (Z3 AST) -> IO Expr
z3Satisfiable expr varmap = do
  evalZ3 script >>= \case
    Sat -> return expr
    _ -> return (LitB False)
  where
    script = do
      reset
      push
      assert =<< evalExpr expr varmap
      check

addExprVariable :: (Map String Expr, Map String Type) -> VarDeclaration -> (Map String Expr, Map String Type)
addExprVariable (map, ts) (VarDeclaration name t@(PType _)) = (insert name (Var name) map, insert name t ts)
addExprVariable (map, ts) (VarDeclaration name t@(AType _)) = (insert name (Var name) (insert ("#" ++ name) (Var ("#" ++ name)) map), insert name t (insert ("#" ++ name) (PType PTInt) ts))
addExprVariable _ (VarDeclaration _ t) = error $ "This program does not support variables of type " ++ show t
