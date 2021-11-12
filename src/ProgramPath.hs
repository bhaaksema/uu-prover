module ProgramPath where

import GCLParser.GCLDatatype (Stmt (..))

--
-- This file defines types regarding the ProgramPath
--

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