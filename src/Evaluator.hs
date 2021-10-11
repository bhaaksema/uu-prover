{-# LANGUAGE LambdaCase #-}

module Evaluator where

import Data.Map (Map, filter, insert, intersection, toList)
import Data.Maybe (catMaybes)
import GCLParser.GCLDatatype
import ProgramPath (ProgramPath (..), combinePaths)
import WLP (considerExpr, evalExpr, simplifyExpr, traceVarExpr, wlp)
import Z3.Monad

evaluateFullTree :: ProgramPath Expr -> [(Map String Expr -> Expr, ProgramPath Expr)]
evaluateFullTree treepath@(TreePath cond stmts option1 option2)
  | cond == LitB False = []
  | otherwise = do
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
evaluateFullTree linpath@(LinearPath cond stmts)
  | cond == LitB False = []
  | otherwise = do
    let path = wlp stmts (\v -> LitB True)
    let condExpr = considerExpr cond
    [(\vars -> simplifyExpr (BinopExpr Implication (condExpr vars) (path vars)), linpath)]
evaluateFullTree (EmptyPath cond) = [(const cond, EmptyPath cond)]
evaluateFullTree InvalidPath = [(const (LitB False), InvalidPath)]

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
calcWLP :: ProgramPath Expr -> Map String Expr -> [(Expr, ProgramPath Expr)]
calcWLP tree vars = do
  let wlpsAndTrees = evaluateFullTree tree
  map (\(expr, path) -> (simplifyExpr (expr vars), path)) wlpsAndTrees

-- Outputs if an expression can be contradicted. If so, also outputs how
verifyExpr :: Expr -> (Map String (Z3 AST), Map String Type) -> IO Result
verifyExpr expr (z3vars, types) =
  evalZ3 script >>= \(result, sol) ->
    case result of
      Sat -> do
        putStrLn "counterexample found: "
          >> putStrLn "ints, bools, arrays"
          >> putStrLn (show (map fst (toList intNames)) ++ show (map fst (toList boolNames)) ++ show (map fst (toList arrayNames)))
          >> putStrLn sol
          >> putStrLn []
        return result
      _ -> return result
  where
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
z3Script :: Expr -> Map String (Z3 AST) -> Z3 AST
z3Script = evalExpr

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
