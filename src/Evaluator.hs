{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Evaluator where

import Data.Map (Map, empty, filter, fromList, insert, intersection, keys, mapWithKey, toList, (!))
import qualified Data.Map (map)
import Data.Maybe (catMaybes, fromMaybe)
import GCLParser.GCLDatatype
import ProgramPath (ProgramPath (..), combinePaths, unrollSeq)
import WLP (PostConditions, considerExpr, evalExpr, simplifyExpr, traceVarExpr, wlp)
import Z3.Monad

evaluateFullTree :: ProgramPath Expr -> PostConditions -> [(Map String Expr -> (Expr, Map String Expr), [Stmt])]
evaluateFullTree treepath@(TreePath cond stmts option1 option2) postConds@(postCond, errorCond)
  | cond == LitB False = []
  | otherwise = do
    let expr1 = evaluateFullTree option1 postConds
    let expr2 = evaluateFullTree option2 postConds
    -- Calculates the wlp over branch node statements
    -- If it has statements, runs wlp using the precondition of expr1, else just returns that precondition
    let wlps1 = map concatPaths expr1
    let wlps2 = map concatPaths expr2
    wlps1 ++ wlps2
  where
    myPath = maybe [] unrollSeq stmts
    myStmts = maybe Skip (Seq (Assume cond)) stmts
    concatPaths (wlpAndVars, path) = (wlp myStmts (wlpAndVars, errorCond), myPath ++ path)
evaluateFullTree whilepath@(AnnotedWhilePath invar guard whilePath nextPath) (postCond, errorCond) = do
  let wlpsOverS = evaluateFullTree whilePath (\vars -> (considerExpr invar vars, vars), errorCond)
  let qs = evaluateFullTree nextPath (postCond, errorCond)

  -- Create all possible combinations of the inner while path and the next path.
  -- Note that all possible combinations need to be checked, as we don't know in advance whether there is an unannoted while within this while.
  -- Moreover other branching structures need to be evaluated as well (like if-then-else).
  let combos = [(setup whilePath wlpOverS q, whilePath ++ nextPath) | (wlpOverS, whilePath) <- wlpsOverS, (q, nextPath) <- qs]
  combos
  where
    setup whilePath wlpOverS qAndVars vars = do
      let newVars = freshenModifiedVars whilePath vars
      let q = fst . qAndVars

      let wlpOverSEvaluated = fst $ wlpOverS newVars
      let iAndNotG = BinopExpr And invar (OpNeg guard)
      let iAndG = BinopExpr And invar guard
      let iNotGImpliesQ = BinopExpr Implication iAndNotG (q newVars)
      let iGImpliesWlp = BinopExpr Implication iAndG wlpOverSEvaluated

      -- An invariant is valid only if i /\ g => wlp S I AND i /\ ~g => Q AND i = True
      let evaluatedInvar = considerExpr invar vars
      let validInvar = considerExpr (BinopExpr And evaluatedInvar (BinopExpr And iNotGImpliesQ iGImpliesWlp)) newVars
      let triggerExc = q (insert "exc" (LitI 3) vars) -- Run rest of program, but with exception set to 3
      let invarIfValid = BinopExpr And (BinopExpr Implication validInvar evaluatedInvar) (BinopExpr Implication (OpNeg validInvar) triggerExc)

      let oldExcZero = BinopExpr Equal (vars ! "exc") (LitI 0)
      let newExcValue = NewStore (RepBy (BinopExpr Or validInvar (OpNeg oldExcZero)) (vars ! "exc") (LitI 3))
      let finalVars = insert "exc" newExcValue vars
      (invarIfValid, finalVars)

    -- This function goes through a list of statements and adds variables that are assigned to as a fresh variable a map of existing variables.
    -- This is used to evaluate the variables in i /\ g = wlp and i /\ ~g => Q as fresh variables, as is required to evaluate these expressions correctly.
    freshenModifiedVars [] vars = vars
    freshenModifiedVars (Assign name _ : stmts) vars = insert name (Var name) (freshenModifiedVars stmts vars)
    freshenModifiedVars (_ : stmts) vars = freshenModifiedVars stmts vars
evaluateFullTree whilepath@(TryCatchPath tryPath eName catchPath nextPath) (postCond, errorCond) = do
  let qs = evaluateFullTree nextPath (postCond, errorCond)
  -- All combinations of catchPaths and nextPaths
  let catchWlps' = [map (\(catchWlp, catchPath) -> (catchWlp, q, catchPath ++ nextPath)) $ evaluateFullTree catchPath (q, errorCond) | (q, nextPath) <- qs]
  let catchWlps = concat catchWlps'

  -- All combinations of tryPaths and handeling paths
  let tryWlps' = [map (\(tryWlp, tryPath) -> (tryWlp, tryPath ++ postPath)) $ evaluateFullTree tryPath (q, resetExc catchWlp) | (catchWlp, q, postPath) <- catchWlps]
  let tryWlps = concat tryWlps'
  tryWlps
  where
    resetExc wlp = \vars -> (wlp . insert "exc" (LitI 0) . insert eName (vars ! "exc")) vars --Stores the exc code in the eName variable as defined in the catch, and resets exc to 0
evaluateFullTree linpath@(LinearPath cond stmts) postConds
  | cond == LitB False = []
  | otherwise = do
    let path = wlp stmts postConds -- Postcondition is: exception must be code 0 (no exception)
    let condExpr = considerExpr cond
    [(\vars -> (simplifyExpr (BinopExpr Implication (condExpr vars) (fst (path vars))), snd (path vars)), unrollSeq stmts)]
evaluateFullTree (EmptyPath cond) postConds = [(\vars -> (cond, vars), [])]
evaluateFullTree InvalidPath _ = [] --Ignore invalid path

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
evaluateTreeConds path@TryCatchPath {} vars varmap = return path -- Note that no path can be evaluated anymore now! There could be many possibilities of variables changing inside of the tryPath if it has an error inside it.
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
calcWLP :: ProgramPath Expr -> Map String Expr -> [((Expr, Map String Expr), [Stmt])]
calcWLP tree vars = do
  let postCondition = BinopExpr Equal (Var "exc") (LitI 0) -- Postcondition is: there was no error
  let wlpPostCondition = \vars -> (considerExpr postCondition vars, vars) -- Postcondition formualted as a function that the wlp function is able to handle
  let wlpsAndTrees = evaluateFullTree tree (wlpPostCondition, wlpPostCondition)
  map (\(exprAndVars, path) -> (simplify $ exprAndVars vars, path)) wlpsAndTrees
  where
    simplify (expr, vars) = (simplifyExpr expr, vars)

-- Outputs if an expression can be contradicted. If so, also outputs how
verifyExpr :: Expr -> (Map String (Z3 AST), Map String Expr, Map String Type) -> IO (Result, Integer)
verifyExpr expr (z3vars, finalVarsExpr, types) =
  evalZ3 script >>= \(result, intMaybe, finalIntMaybe, boolMaybe, finalBoolMaybe, arrayMaybe) ->
    case result of
      Sat -> do
        let intValueMap = fromList $ zip (keys intNames) (fromMaybe [] intMaybe) -- Map of (name, Integer), allows us to get array lengths (using #name)
        let arrays = map (fromMaybe []) arrayMaybe -- Map the fromMaybe function over all the arrays. Should be safe as it is only nothing when there is no counter example
        let arraysWithNames = zip (map fst (toList arrayNames)) arrays -- Make a list of tuples, so that the name of each array is available (i.e. [(arrayname, array)])
        let arrayValues = map (\(name, array) -> getFirstN (intValueMap ! ("#" ++ name)) array) arraysWithNames -- Get the first #name elements of the infinite z3 array.
        putStrLn "counterexample found: "
          >> putStrLn "ints"
          >> print (map fst (toList intNames))
          >> putStr (unMaybe intMaybe)
          >> putStrLn " (Input values)"
          >> putStr (unMaybe finalIntMaybe)
          >> putStrLn " (Estimate of final values)"
          >> putStrLn []
          >> putStrLn "bools"
          >> print (map fst (toList boolNames))
          >> putStr (unMaybe boolMaybe)
          >> putStrLn " (Input values)"
          >> putStr (unMaybe finalBoolMaybe)
          >> putStrLn " (Estimate of final values)"
          >> putStrLn []
          >> putStrLn "arrays (only input values)"
          >> print (map fst (toList arrayNames))
          >> print arrayValues
          >> putStrLn []
        let excValue = fromList (zip (keys intNames) (fromMaybe [] finalIntMaybe)) ! "exc"
        return (result, excValue)
      _ -> return (result, 0) -- Since no counterexample was found, the postcondition of exc == 0 was satisfied and exc must equal 0
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

      newVars <- mapM snd (toList finalInts)
      (_, finalIntMaybe) <- withModel $ \m ->
        catMaybes <$> mapM (evalInt m) newVars

      let arrayNames = map fst (toList z3Arrays)
      arrayElements <- mapM (\name -> sequence (createArrayGetter name 0)) arrayNames
      arrayMaybe' <- mapM (\a -> withModel $ \m -> catMaybes <$> mapM (evalInt m) a) arrayElements
      let arrayMaybe = map snd arrayMaybe'

      newVars <- mapM snd (toList z3Bools)
      (result, boolMaybe) <- withModel $ \m ->
        catMaybes <$> mapM (evalBool m) newVars

      newVars <- mapM snd (toList finalBools)
      (_, finalBoolMaybe) <- withModel $ \m ->
        catMaybes <$> mapM (evalBool m) newVars
      return (result, intMaybe, finalIntMaybe, boolMaybe, finalBoolMaybe, arrayMaybe)

    -- Dicts of z3 variables that have only a specific type
    finalVars = Data.Map.map (`evalExpr` z3vars) finalVarsExpr
    (z3Ints, finalInts) = (intersection z3vars intNames, intersection finalVars intNames)
    (z3Bools, finalBools) = (intersection z3vars boolNames, intersection finalVars boolNames)
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
