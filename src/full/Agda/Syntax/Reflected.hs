{-# OPTIONS_GHC -fwarn-missing-signatures #-}

module Agda.Syntax.Reflected where

import Data.Text (Text)

import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Internal (Dom)

import Agda.Utils.List1 (List1, pattern (:|))
import qualified Agda.Utils.List1 as List1

type Args       = [Arg Term]

data Elim' a = Apply (Arg a) -- no record projections for now
  deriving (Show)
type Elim = Elim' Term
type Elims = [Elim]

argsToElims :: Args -> Elims
argsToElims = map Apply

data Abs a = Abs String a
  deriving (Show)

data Term = Var Int Elims
          | Con QName Elims
          | Def QName Elims
          | Meta MetaId Elims
          | Lam Hiding (Abs Term)
          | ExtLam (List1 Clause) Elims
          | Pi (Dom Type) (Abs Type)
          | Sort Sort
          | Lit Literal
          | Unknown
  deriving (Show)

type Type = Term

data Sort = SetS Term
          | LitS Integer
          | UnknownS
  deriving (Show)

data Pattern = ConP QName [Arg Pattern]
             | DotP Term
             | VarP Int
             | LitP Literal
             | AbsurdP
             | ProjP QName
  deriving (Show)

data Clause
  = Clause
    { clauseTel  :: [(Text, Arg Type)]
    , clausePats :: [Arg Pattern]
    , clauseRHS  :: Term
    }
  | AbsurdClause
    { clauseTel  :: [(Text, Arg Type)]
    , clausePats :: [Arg Pattern]
    }
  deriving (Show)

data Definition = FunDef Type [Clause]
                | DataDef   -- nothing for now
                | RecordDef -- nothing for now
                | DataConstructor
                | Axiom
                | Primitive
  deriving (Show)
