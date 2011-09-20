{-# LANGUAGE CPP, DeriveFunctor #-}

module Agda.TypeChecking.Coverage.Match where

import Control.Applicative
import Control.Monad.State
import Data.Monoid
import Data.Traversable (traverse)
import Data.Function

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Literal

import Agda.Utils.Permutation
import Agda.Utils.Size

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | We use a special representation of the patterns we're trying to match
--   against a clause. In particular we want to keep track of which variables
--   are blocking a match.
data MPat = VarMP Nat | ConMP QName [Arg MPat] | LitMP Literal | WildMP

buildMPatterns :: Permutation -> [Arg Pattern] -> [Arg MPat]
buildMPatterns perm ps = evalState (mapM (traverse build) ps) xs
  where
    xs   = permute (invertP perm) $ reverse [0 .. size perm - 1]
    tick = do x : xs <- get; put xs; return x

    build (VarP _)        = VarMP <$> tick
    build (ConP con _ ps) = ConMP con <$> mapM (traverse build) ps
    build (DotP t)        = tick *> buildT t
    build (LitP l)        = return $ LitMP l

    buildT (Con c args)   = ConMP c <$> mapM (traverse buildT) args
    buildT (Var i [])     = return (VarMP i)
    buildT _              = return WildMP

-- | If matching is inconclusive (@Block@) we want to know which
--   variable is blocking the match. If a dot pattern is blocking a match
--   we're screwed.
data Match a = Yes a | No | Block (Maybe Nat)
  deriving (Functor)

instance Monoid a => Monoid (Match a) where
  mempty                    = Yes mempty
  Yes a   `mappend` Yes b   = Yes $ mappend a b
  Yes _   `mappend` No      = No
  Yes _   `mappend` Block x = Block x
  No      `mappend` _       = No
  Block x `mappend` _       = Block x

choice :: Match a -> Match a -> Match a
choice (Yes a) _   = Yes a
choice (Block x) _ = Block x
choice No m        = m

type MatchLit = Literal -> MPat -> Match ()

noMatchLit :: MatchLit
noMatchLit _ _ = No

yesMatchLit :: MatchLit
yesMatchLit _ VarMP{}  = Yes ()
yesMatchLit _ WildMP{} = Yes ()
yesMatchLit _ _        = No

-- | Match the given patterns against a list of clauses
match :: [Clause] -> [Arg Pattern] -> Permutation -> Match Nat
match cs ps perm = foldr choice No $ zipWith matchIt [0..] cs
  where
    mps = buildMPatterns perm ps

    -- If liberal matching on literals fails or blocks we go with that.
    -- If it succeeds we use the result from conservative literal matching.
    -- This is to make sure that we split enough when literals are involved.
    -- For instance,
    --    f ('x' :: 'y' :: _) = ...
    --    f (c :: s) = ...
    -- would never split the tail of the list if we only used conservative
    -- literal matching.
    matchIt i c = matchClause yesMatchLit mps i c +++
                  matchClause noMatchLit  mps i c

    Yes _   +++ m = m
    No      +++ _ = No
    Block x +++ _ = Block x

-- | Check if a clause could match given generously chosen literals
matchLits :: Clause -> [Arg Pattern] -> Permutation -> Bool
matchLits c ps perm = case matchClause yesMatchLit (buildMPatterns perm ps) 0 c of
  Yes _ -> True
  _     -> False

matchClause :: MatchLit -> [Arg MPat] -> Nat -> Clause -> Match Nat
matchClause mlit qs i c = fmap (const i) $ matchPats mlit (clausePats c) qs

matchPats :: MatchLit -> [Arg Pattern] -> [Arg MPat] -> Match ()
matchPats mlit ps qs = mconcat $ zipWith (matchPat mlit) (map unArg ps) (map unArg qs)

matchPat :: MatchLit -> Pattern -> MPat -> Match ()
matchPat _    (VarP _) _ = Yes ()
matchPat _    (DotP _) _ = Yes ()
matchPat mlit (LitP l) q = mlit l q
matchPat mlit (ConP c _ ps) q = case q of
  VarMP x -> Block $ Just x
  WildMP  -> Block Nothing
  ConMP c' qs
    | c == c'   -> matchPats mlit ps qs
    | otherwise -> No
  LitMP _ -> __IMPOSSIBLE__
