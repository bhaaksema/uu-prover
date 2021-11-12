module ProgramPathPrinter where

import ProgramPath
import ProgramPathOps (splitDepth, totalDepth)

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