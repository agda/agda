{-# OPTIONS -fglasgow-exts -fno-warn-incomplete-patterns #-}

{- Notes

  I intend to break the code at the bottom of this file into separate
  modules after I complete some basic functionality (reduction, and
  maybe equality). I am developing it in one file for the moment
  because it is far easier to see everyhting in front of me and I'm
  not yet sure how I want to break things up (and I don't want to
  hassle with moving files around the CVS repository).

  I am intentionally not writing catch-all cases for graceful internal
  error recovery. This can be done later after some testing and when
  there is a more concrete notion of how we'll handle errors.

-}

module Syntax.InternalNew where

import Debug.Trace

import qualified Data.List as L
import Data.Generics
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Error

import Syntax.Common
import Syntax.Position
import Syntax.Abstract.Name
import Syntax.Literal

-- | this instance declaration is used in flex-flex unifier case
--
instance Eq Value where
    Var i [] == Var j [] = i == j
    v1       == v2       = False


--------------------------------------------------------------
--
-- Stuff which might be better off in other files.
--
--------------------------------------------------------------


---------------------------------------------------------------------------
--
-- Example
--
test x = runReaderT (runStateT (do x; applyStore) testSt{sigSt = []}) []

newmetaT = newMeta (\x -> MetaT x []) $ UnderScoreT Prop []
newmetaV = newMeta (\x -> MetaV x []) $ UnderScoreV set0 []
eqTest = do
    x <- newmetaV
    equalVal Why set0 x x
    y <- newmetaV
    equalVal Why (arr set0 $ arr set0 set0) (lam $ lam $ app (app x $ Var 0 []) $ Var 1 [])
                                            (lam $ lam $ app (app y $ Var 0 []) $ Var 1 [])
eqTest1 = do
    x <- newmetaV
    y <- newmetaV
    equalVal Why (arr set0 $ arr set0 set0) (lam $ lam $ app (app x $ Var 0 []) $ Var 1 [])
                                            (lam $ app y $ Var 0 [])
eqTest2 = do
    x <- newmetaV
    y <- newmetaV
    equalVal Why (arr set0 $ arr set0 set0) (lam $ app y $ Var 0 [])
                                            (lam $ lam $ app (app x $ Var 0 []) $ Var 1 [])

eqTest3 = do
    x <- newmetaV
    equalVal Why (arr set0 $ arr set0 $ arr set0 set0) (lam $ lam $ lam $ app (app x $ Var 0 []) $ Var 1 [])
                                                       (lam $ lam $ lam $ app (app x $ Var 1 []) $ Var 2 [])

eqTest4 = do
    x <- newmetaV
    y <- newmetaV
    equalVal Why (arr set0 $ arr set0 $ arr set0 set0) (lam $ lam $ lam $ app (app x $ Var 0 []) $ Var 1 [])
                                                       (lam $ lam $ lam $ app (app y $ Var 1 []) $ Var 2 [])

{-
eqTest5 = do
    x <- newmetaT
    y <- newmetaT
    equalTyp Why (lam $ lam $ lam $ app (app x $ Var 0 []) $ Var 1 [])
                 (lam $ lam $ lam $ app (app y $ Var 1 []) $ Var 2 [])
-}

lam v = Lam (Abs noName v) []
app x y = addArgs [y] x
arr x y = Pi x $ Abs noName y
   

testRed v = runReaderT (evalStateT (reduceM v) testSt) []

normalize :: GenericM TCM
normalize v = walk (mkM trmFun `extM` typFun) v where
    trmFun v = lift $ lift  $ reduceM v
    typFun a = lift $ lift $ instType a

testNrm v = runReaderT (evalStateT (normalize v) testSt) []

applyStore = do 
    st <- gets metaSt 
    st' <- normalize st 
    modify (\x -> x{metaSt= st'})

testSt = TCSt {
  genSymSt = 0,
  metaSt   = [],
  cnstrSt  = [],
  sigSt    = testSig
 }

testSig = [

  -- nat : set_0
  Decl (Name noRange "nat") (Sort (Type 0)) 
    (Just [Name noRange "Z", Name noRange "S"]),

  -- Z : nat
  Decl (Name noRange "Z") (El (Def (QName $ Name noRange "nat") []) (Type 0)) 
    Nothing,
  Defn (Name noRange "Z") [],

  -- S : nat -> nat
  Decl (Name noRange "S") (
    Pi (El (Def (QName $ Name noRange "nat") []) (Type 0)) 
       (Abs (Name noRange "_") $ El (Def (QName $ Name noRange "nat") []) (Type 0)) 
       
  ) Nothing,
  Defn (Name noRange "S") [],

  -- plus : nat -> nat -> nat
  Decl (Name noRange "plus") (
    Pi (El (Def (QName $ Name noRange "nat") []) (Type 0)) (Abs (Name noRange "_") $
    Pi (El (Def (QName $ Name noRange "nat") []) (Type 0)) (Abs (Name noRange "_") $
    El (Def (QName $ Name noRange "nat") []) (Type 0))) 
  ) Nothing,

  Defn (Name noRange "plus") [ 

    -- plus Z n = n
    Clause [ConP (QName $ Name noRange "Z") [], VarP $ Name noRange "n"] $ 
      Bind $ Abs (Name noRange "n") $ Body $ Var 0 [],

    -- plus (S m) n = S (plus m n)
    Clause 
      [ConP (QName $ Name noRange "S") [VarP $ Name noRange "m"], VarP $ Name noRange "n"] $ 
      Bind $ Abs (Name noRange "m") $ Bind $ Abs (Name noRange "n") $ 
      Body $ 
        Def (QName $ Name noRange "S") [Def (QName $ Name noRange "plus") [Var 1 [], Var 0 []]] 
  ]
 ]

s = Def (QName $ Name noRange "S")
z = Def (QName $ Name noRange "Z") []
plus = Def (QName $ Name noRange "plus")

two = s [s [z]]
three = s [s [s [z]]]


