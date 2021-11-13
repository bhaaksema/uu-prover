{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Evaluator where

import Data.Map (Map, empty, filter, fromList, insert, intersection, keys, mapWithKey, toList, (!))
import qualified Data.Map (map)
import Data.Maybe (catMaybes, fromMaybe)
import ExpressionOps (considerExpr, simplifyExpr, updateExc)
import GCLParser.GCLDatatype
import GeneralTypes
import ProgramPath (ProgramPath (..))
import StatementOps (unrollSeq)
import Transformer (evalExpr)
import WLP (traceVarExpr, wlp)
import Z3.Monad

-- Will recursively find all WLPS that can be generated in the given path tree
findTreeWLPS :: ProgramPath Expr -> PostConditions -> [(WLPType, PathStatements)]
findTreeWLPS treepath@(BranchPath cond stmts option1 option2) postConds@(postCond, errorCond)
  | cond == LitB False = []
  | otherwise = do
    let expr1 = findTreeWLPS option1 postConds
    let expr2 = findTreeWLPS option2 postConds
    -- Calculates the wlp over branch node statements
    -- If it has statements, runs wlp using the precondition of expr1, else just returns that precondition
    let wlps1 = map concatPaths expr1
    let wlps2 = map concatPaths expr2
    wlps1 ++ wlps2
  where
    myPath = maybe [] unrollSeq stmts
    myStmts = maybe Skip (Seq (Assume cond)) stmts
    concatPaths (wlpAndVars, path) = (wlp myStmts (wlpAndVars, errorCond), myPath ++ path)
findTreeWLPS whilepath@(AnnotedWhilePath invar guard whilePath nextPath) (postCond, errorCond) = do
  let wlpsOverS = findTreeWLPS whilePath (\vars -> (considerExpr invar vars, vars), errorCond)
  let qs = findTreeWLPS nextPath (postCond, errorCond)

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

      let finalVars = updateExc (OpNeg validInvar) (LitI 3) vars
      (invarIfValid, finalVars)

    -- This function goes through a list of statements and adds variables that are assigned to as a fresh variable a map of existing variables.
    -- This is used to evaluate the variables in i /\ g = wlp and i /\ ~g => Q as fresh variables, as is required to evaluate these expressions correctly.
    freshenModifiedVars [] vars = vars
    freshenModifiedVars (Assign name _ : stmts) vars = insert name (Var name) (freshenModifiedVars stmts vars)
    freshenModifiedVars (_ : stmts) vars = freshenModifiedVars stmts vars
findTreeWLPS whilepath@(TryCatchPath tryPath eName catchPath nextPath) (postCond, errorCond) = do
  let qs = findTreeWLPS nextPath (postCond, errorCond)
  -- All combinations of catchPaths and nextPaths
  let catchWlps' = [map (\(catchWlp, catchPath) -> (catchWlp, q, catchPath ++ nextPath)) $ findTreeWLPS catchPath (q, errorCond) | (q, nextPath) <- qs]
  let catchWlps = concat catchWlps'

  -- All combinations of tryPaths and handeling paths
  let tryWlps' = [map (\(tryWlp, tryPath) -> (tryWlp, tryPath ++ postPath)) $ findTreeWLPS tryPath (q, resetExc catchWlp) | (catchWlp, q, postPath) <- catchWlps]
  let tryWlps = concat tryWlps'
  tryWlps
  where
    resetExc wlp = \vars -> (wlp . insert "exc" (LitI 0) . insert eName (vars ! "exc")) vars --Stores the exc code in the eName variable as defined in the catch, and resets exc to 0
findTreeWLPS linpath@(LinearPath cond stmts) postConds
  | cond == LitB False = []
  | otherwise = do
    let path = wlp (Seq (Assume cond) stmts) postConds -- Postcondition is: exception must be code 0 (no exception)
    [(path, unrollSeq stmts)]
findTreeWLPS (EmptyPath cond) postConds = [(\vars -> (cond, vars), [])]
findTreeWLPS InvalidPath _ = [] --Ignore invalid path

-- First finds all WLPS of the tree, then applies the given variable map. Returns the expression-evaluated wlps and their paths.
calcWLP :: ProgramPath Expr -> GCLVars -> [((Expr, GCLVars), PathStatements)]
calcWLP tree vars = do
  let postCondition = BinopExpr Equal (Var "exc") (LitI 0) -- Postcondition is: there was no error
  let wlpPostCondition = \vars -> (considerExpr postCondition vars, vars) -- Postcondition formualted as a function that the wlp function is able to handle
  let wlpsAndTrees = findTreeWLPS tree (wlpPostCondition, wlpPostCondition)
  map (\(exprAndVars, path) -> (simplify $ exprAndVars vars, path)) wlpsAndTrees
  where
    simplify (expr, vars) = (simplifyExpr expr, vars)

-- Outputs if an expression can be contradicted. If so, also outputs how
verifyExpr :: Expr -> (Z3Vars, GCLVars, VarTypes) -> IO (Result, ExceptionCode)
verifyExpr expr (z3vars, finalVarsExpr, types) =
  evalZ3 script >>= \(result, intMaybe, finalIntMaybe, boolMaybe, finalBoolMaybe, arrayMaybe) ->
    case result of
      Sat -> do
        let intValueMap = fromList $ zip (keys intNames) (fromMaybe [] intMaybe) -- Map of (name, Integer), allows us to get array lengths (using #name)
        let arrays = map (fromMaybe []) arrayMaybe -- Map the fromMaybe function over all the arrays. Should be safe as it is only nothing when there is no counter example
        let arraysWithNames = zip (map fst (toList arrayNames)) arrays -- Make a list of tuples, so that the name of each array is available (i.e. [(arrayname, array)])
        let arrayValues = map (\(name, array) -> getFirstN (intValueMap ! ("#" ++ name)) array) arraysWithNames -- Get the first #name elements of the infinite z3 array.
        let excValue = fromList (zip (keys intNames) (fromMaybe [] finalIntMaybe)) ! "exc"

        printCounterexample (intNames, boolNames, arrayNames) (intMaybe, finalIntMaybe, boolMaybe, finalBoolMaybe, arrayValues)
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

    -- Create an array of integer variables, so that all values can be extracted from array
    createArrayGetter arrayName 999 = []
    createArrayGetter arrayName i = do
      getArrayElem arrayName i : createArrayGetter arrayName (i + 1)

    -- Selects item with given index from the array with given name
    getArrayElem arrayName index = do
      array <- z3Arrays ! arrayName
      i <- mkInteger $ index - 1
      mkSelect array i

-- Will print all the values of the counterexample to the console
printCounterexample :: (VarTypes, VarTypes, VarTypes) -> (Maybe [Integer], Maybe [Integer], Maybe [Bool], Maybe [Bool], [[Integer]]) -> IO ()
printCounterexample (intNames, boolNames, arrayNames) (intMaybe, finalIntMaybe, boolMaybe, finalBoolMaybe, arrayValues) = do
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
  where
    unMaybe m = maybe "" show m -- Turn the maybe into a string

-- Given maps of existing variables and types, adds the variable from a VarDeclaration to these maps.
addExprVariable :: (GCLVars, VarTypes) -> VarDeclaration -> (GCLVars, VarTypes)
addExprVariable (map, ts) (VarDeclaration name t@(PType _)) = (insert name (Var name) map, insert name t ts)
addExprVariable (map, ts) (VarDeclaration name t@(AType _)) = (insert name (Var name) (insert ("#" ++ name) (Var ("#" ++ name)) map), insert name t (insert ("#" ++ name) (PType PTInt) ts))
addExprVariable _ (VarDeclaration _ t) = error $ "This program does not support variables of type " ++ show t
