{-# OPTIONS -fglasgow-exts #-}

module Agda.Auto.Syntax where

import Data.IORef

import Agda.Auto.NarrowingSearch


data RefInfo o = RIEnv [ConstRef o]
               | RIMainInfo Nat (HNExp o)
               | forall a . RIUnifInfo (Metavar a (RefInfo o)) [CAction o] (HNExp o)  -- metavar is the flexible side of the equality

type MyPB o = PB (RefInfo o)
type MyMB a o = MB a (RefInfo o)

type Nat = Int

data FMode = Hidden
           | NotHidden
 deriving Eq

data MId = Id String
         | NoId

data Abs a = Abs MId a

data ConstDef o = ConstDef {cdname :: String, cdorigin :: o, cdtype :: MExp o, cdcont :: DeclCont o}  -- contains no metas

data DeclCont o = Def Nat [Clause o]
                | Datatype [ConstRef o]  -- constructors
                | Constructor
                | Postulate

type Clause o = ([Pat o], MExp o)

data Pat o = PatConApp (ConstRef o) [Pat o]
           | PatVar
           | PatExp

type ConstRef o = IORef (ConstDef o)

data Elr o = Var Nat
           | Const (ConstRef o)

data Sort = SortLevel Nat
          | Type

data Exp o = App (Elr o) (MArgList o)
           | Lam FMode (Abs (MExp o))
           | Fun FMode (MExp o) (MExp o)
           | Pi FMode (MExp o) (Abs (MExp o))
           | Sort Sort

type MExp o = MM (Exp o) (RefInfo o)

data ArgList o = ALNil
               | ALCons FMode (MExp o) (MArgList o)
               | ALConPar (MArgList o)  -- inserted to cover glitch of polymorphic constructor applications coming from Agda

type MArgList o = MM (ArgList o) (RefInfo o)

data HNExp o = HNApp (Elr o) (CArgList o)
             | HNLam (Abs (CExp o))
             | HNFun FMode (CExp o) (CExp o)
             | HNPi FMode (CExp o) (Abs (CExp o))
             | HNSort Sort

data HNArgList o = HNALNil
                 | HNALCons (CExp o) (CArgList o)
                 | HNALConPar (CArgList o)

type CExp o = Clos (MExp o) o

data CArgList o = CALNil
                | CALConcat (Clos (MArgList o) o) (CArgList o)
 -- !! (CALCons and CALConcat are used differently by eta rule in hncomp, but could replace those uses by a new CALSnoc construction)

data Clos a o = Clos [CAction o] a

data CAction o = Sub (CExp o)
               | Skip
               | Weak Nat

type Ctx o = [(MId, CExp o)]

type EE = IO

data Elrs o = ElrsNil
            | ElrsCons (Elr o) (Elrs o)
            | ElrsWeak (Elrs o)


