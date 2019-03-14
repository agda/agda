{-# OPTIONS_GHC -fwarn-missing-signatures #-}

module Agda.Syntax.Reflected where

import Agda.Syntax.Common
import Agda.Syntax.Literal
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Internal (Dom)

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
          | ExtLam [Clause] Elims
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
             | DotP
             | VarP String
             | LitP Literal
             | AbsurdP
             | ProjP QName
  deriving (Show)

data Clause = Clause [Arg Pattern] Term | AbsurdClause [Arg Pattern]
  deriving (Show)

data Definition = FunDef Type [Clause]
                | DataDef   -- nothing for now
                | RecordDef -- nothing for now
                | DataConstructor
                | Axiom
                | Primitive
  deriving (Show)
