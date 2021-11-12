module StatementOps where

import GCLParser.GCLDatatype
import GeneralTypes

--
-- These functions define simple operations over statements and lists of statements
--

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