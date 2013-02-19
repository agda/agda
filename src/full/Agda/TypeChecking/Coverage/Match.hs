{-# LANGUAGE CPP, PatternGuards, DeriveFunctor #-}

module Agda.TypeChecking.Coverage.Match where

import Control.Applicative
import Control.Monad.State

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Traversable (traverse)
import Data.Function

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern
import Agda.Syntax.Literal

import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.List

#include "../../undefined.h"
import Agda.Utils.Impossible

{-| Given

    1. the function clauses @cs@
    2. the patterns @ps@ and permutation @perm@ of a split clause

we want to compute a variable index of the split clause to split on next.

First, we find the set @cs'@ of all the clauses that are
instances (via substitutions @rhos@) of the split clause.

In these substitutions, we look for a column that has only constructor patterns.
We try to split on this column first.
-}
{-
nonOverlappingCompleteMatches :: [Clause] -> [Arg Pattern] -> Permutation -> Match Nat
nonOverlappingCompleteMatches cs ps perm
-}

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

-- | We use a special representation of the patterns we're trying to match
--   against a clause. In particular we want to keep track of which variables
--   are blocking a match.
data MPat = VarMP Nat | ConMP QName [Arg MPat] | LitMP Literal | WildMP

buildMPatterns :: Permutation -> [Arg Pattern] -> [Arg MPat]
buildMPatterns perm ps = evalState (mapM (traverse build) ps) xs
  where
    xs   = permute (invertP perm) $ downFrom (size perm)  -- reverse [0 .. size perm - 1]
    tick = do x : xs <- get; put xs; return x

    build (VarP _)        = VarMP <$> tick
    build (ConP con _ ps) = ConMP con <$> mapM (traverse build) ps
    build (DotP t)        = tick *> buildT t
    build (LitP l)        = return $ LitMP l

    buildT (Con c args)   = ConMP c <$> mapM (traverse buildT) args
    buildT (Var i [])     = return (VarMP i)
    buildT _              = return WildMP


-- | If matching is inconclusive (@Block@) we want to know which
--   variables are blocking the match.
data Match a
  = Yes a                -- ^ Matches unconditionally.
  | No                   -- ^ Definitely does not match.
  | Block BlockingVars   -- ^ Could match if non-empty list of blocking variables
                         --   is instantiated properly.
  deriving (Functor)

-- | @Nothing@ means there is an overlapping match for this variable.
--   @Just cons@ means that it is an non-overlapping match and
--   @cons@ are the encountered constructors.
type BlockingVar  = (Nat, (Maybe [QName]))
type BlockingVars = [BlockingVar]

overlapping :: BlockingVars -> BlockingVars
overlapping = map $ \ (x, _) -> (x, Nothing)

-- | Left dominant merge of blocking vars.
zipBlockingVars :: BlockingVars -> BlockingVars -> BlockingVars
zipBlockingVars xs ys = map upd xs
  where
    upd (x, Just cons) | Just (Just cons') <- lookup x ys =
     (x, Just $ cons ++ cons')
    upd (x, _) = (x, Nothing)

-- | @choice m m'@ combines the match results @m@ of a function clause
--   with the (already combined) match results $m'$ of the later clauses.
--   It is for skipping clauses that definitely do not match ('No').
--   It is left-strict, to be used with @foldr@.
--   If one clause unconditionally matches ('Yes') we do not look further.
choice :: Match a -> Match a -> Match a
choice (Yes a)   _         = Yes a
choice (Block x) (Block y) = Block (zipBlockingVars x y)
choice (Block x) (Yes _)   = Block $ overlapping x
choice (Block x) No        = Block x
choice No        m         = m

type MatchLit = Literal -> MPat -> Match ()

noMatchLit :: MatchLit
noMatchLit _ _ = No

yesMatchLit :: MatchLit
yesMatchLit _ VarMP{}  = Yes ()
yesMatchLit _ WildMP{} = Yes ()
yesMatchLit _ _        = No

-- | Check if a clause could match given generously chosen literals
matchLits :: Clause -> [Arg Pattern] -> Permutation -> Bool
matchLits c ps perm =
  case matchClause yesMatchLit (buildMPatterns perm ps) 0 c of
    Yes _ -> True
    _     -> False

-- | @matchClause mlist qs i c@ checks whther clause @c@ number @i@
--   covers a split clause with patterns @qs@.
matchClause :: MatchLit -> [Arg MPat] -> Nat -> Clause -> Match Nat
matchClause mlit qs i c = fmap (const i) $ matchPats mlit (clausePats c) qs

-- | @matchPats mlist ps qs@ checks whether a function clause with patterns
--   @ps@ covers a split clause with patterns @qs@
matchPats :: MatchLit -> [Arg Pattern] -> [Arg MPat] -> Match ()
matchPats mlit ps qs = mconcat $ zipWith (matchPat mlit) (map unArg ps) (map unArg qs)

-- | Combine results of checking whether function clause patterns
--   covers split clause patterns.
--
--   'No' is dominant: if one function clause pattern is disjoint to
--   the corresponding split clause pattern, then
--   the whole clauses are disjoint.
--
--   'Yes' is neutral: for a match, all patterns have to match.
--
--   'Block' accumulates variables of the split clause
--   that have to be instantiated
--   to make the split clause an instance of the function clause.
instance Monoid a => Monoid (Match a) where
  mempty                    = Yes mempty
  Yes a   `mappend` Yes b   = Yes $ mappend a b
  Yes _   `mappend` No      = No
  Yes _   `mappend` Block x = Block x
  No      `mappend` _       = No
  Block x `mappend` Yes b   = Block x
  Block x `mappend` No      = No
  Block x `mappend` Block y = Block $ mappend x y

-- | @matchPat mlit p q@ checks whether a function clause pattern @p@
--   covers a split clause pattern @q@.  There are three results:
--   @Yes ()@ means it covers, because @p@ is a variable
--   pattern or @q@ is a wildcard.
--   @No@ means it does not cover.
--   @Block [x]@ means @p@ is a proper instance of @q@ and could become
--   a cover if @q@ was split on variable @x@.
matchPat :: MatchLit -> Pattern -> MPat -> Match ()
matchPat _    (VarP _) _ = Yes ()
matchPat _    (DotP _) _ = Yes ()
matchPat mlit (LitP l) q = mlit l q
-- matchPat mlit (ConP c (Just _) ps) q | recordPattern ps = Yes ()  -- Andreas, 2012-07-25 record patterns always match!
matchPat mlit (ConP c _ ps) q = case q of
  VarMP x -> Block [(x, Just [c])]
  WildMP  -> Yes ()
  ConMP c' qs
    | c == c'   -> matchPats mlit ps qs
    | otherwise -> No
  LitMP _ -> __IMPOSSIBLE__

{- UNUSED
class RecordPattern a where
  recordPattern :: a -> Bool

instance RecordPattern Pattern where
  recordPattern VarP{} = True
  recordPattern DotP{} = False
  recordPattern LitP{} = False
  recordPattern (ConP _ Nothing _) = False
  recordPattern (ConP _ (Just _) ps) = recordPattern ps

instance RecordPattern a => RecordPattern [a] where
  recordPattern = all recordPattern

instance RecordPattern a => RecordPattern (Arg a) where
  recordPattern = recordPattern . unArg
-}
