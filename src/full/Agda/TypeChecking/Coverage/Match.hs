{-# LANGUAGE CPP           #-}
{-# LANGUAGE DeriveFunctor #-}

module Agda.TypeChecking.Coverage.Match where

import Control.Applicative
import Control.Monad.State

import qualified Data.List as List
import Data.Maybe (mapMaybe, isJust)
import Data.Semigroup (Semigroup, Monoid, (<>), mempty, mappend, mconcat, Any(..))
import Data.Traversable (traverse)

import Agda.Syntax.Abstract (IsProjP(..))
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern ()
import Agda.Syntax.Literal

import Agda.TypeChecking.Substitute

import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.List

#include "undefined.h"
import Agda.Utils.Impossible

{-| Given

    1. the function clauses @cs@
    2. the patterns @ps@

we want to compute a variable index of the split clause to split on next.

First, we find the set @cs'@ of all the clauses that are
instances (via substitutions @rhos@) of the split clause.

In these substitutions, we look for a column that has only constructor patterns.
We try to split on this column first.
-}

-- | Match the given patterns against a list of clauses
match :: [Clause] -> [Arg DeBruijnPattern] -> Match (Nat,[DeBruijnPattern])
match cs ps = foldr choice No $ zipWith matchIt [0..] cs
  where
    -- If liberal matching on literals fails or blocks we go with that.
    -- If it succeeds we use the result from conservative literal matching.
    -- This is to make sure that we split enough when literals are involved.
    -- For instance,
    --    f ('x' :: 'y' :: _) = ...
    --    f (c :: s) = ...
    -- would never split the tail of the list if we only used conservative
    -- literal matching.
    matchIt i c = matchClause yesMatchLit ps i c +++
                  matchClause noMatchLit  ps i c

    Yes _     +++ m = m
    No        +++ _ = No
    m@Block{} +++ _ = m

buildPattern :: Term -> Maybe DeBruijnPattern
buildPattern (Con c args)   = Just $ ConP c noConPatternInfo $ map (fmap $ unnamed . DotP) args
buildPattern (Var i [])     = Just $ debruijnVar i
buildPattern (Shared p)     = buildPattern (derefPtr p)
buildPattern _              = Nothing

isTrivialPattern :: Pattern' a -> Bool
isTrivialPattern VarP{}  = True
isTrivialPattern (ConP c i ps)
 | isJust (conPRecord i) = all isTrivialPattern $ map (namedThing . unArg) ps
 | otherwise             = False
isTrivialPattern LitP{}  = False
isTrivialPattern DotP{}  = True
isTrivialPattern ProjP{} = False -- or True?

-- | If matching is inconclusive (@Block@) we want to know which
--   variables are blocking the match.
data Match a
  = Yes a   -- ^ Matches unconditionally.
  | No      -- ^ Definitely does not match.
  | Block Any BlockingVars
            -- ^ Could match if non-empty list of blocking variables
            --   is instantiated properly.
            --   Also 'Any' is 'True' if all clauses have a result split.
            --   (Only then can we do result splitting.)
  deriving (Functor)

-- | Variable blocking a match.
data BlockingVar  = BlockingVar
  { blockingVarNo   :: Nat
    -- ^ De Bruijn index of variable blocking the match.
  , blockingVarCons :: Maybe [ConHead]
    -- ^ @Nothing@ means there is an overlapping match for this variable.
    --   This happens if one clause has a constructor pattern at this position,
    --   and another a variable.  It is also used for "just variable".
    --
    --   @Just cons@ means that it is an non-overlapping match and
    --   @cons@ are the encountered constructors.
  } deriving (Show)
type BlockingVars = [BlockingVar]

-- | Lens for 'blockingVarCons'.
mapBlockingVarCons :: (Maybe [ConHead] -> Maybe [ConHead]) -> BlockingVar -> BlockingVar
mapBlockingVarCons f b = b { blockingVarCons = f (blockingVarCons b) }

clearBlockingVarCons :: BlockingVar -> BlockingVar
clearBlockingVarCons = mapBlockingVarCons $ const Nothing

overlapping :: BlockingVars -> BlockingVars
overlapping = map clearBlockingVarCons

-- | Left dominant merge of blocking vars.
zipBlockingVars :: BlockingVars -> BlockingVars -> BlockingVars
zipBlockingVars xs ys = map upd xs
  where
    upd (BlockingVar x (Just cons))
      | Just (BlockingVar _ (Just cons')) <- List.find ((x ==) . blockingVarNo) ys
                          = BlockingVar x (Just $ cons ++ cons')
    upd (BlockingVar x _) = BlockingVar x Nothing

-- | @choice m m'@ combines the match results @m@ of a function clause
--   with the (already combined) match results $m'$ of the later clauses.
--   It is for skipping clauses that definitely do not match ('No').
--   It is left-strict, to be used with @foldr@.
--   If one clause unconditionally matches ('Yes') we do not look further.
choice :: Match a -> Match a -> Match a
choice (Yes a)      _            = Yes a
choice (Block r xs) (Block s ys) = Block (Any $ getAny r && getAny s) $
  zipBlockingVars xs ys
choice (Block r xs) (Yes _)      = Block r $ overlapping xs
choice m@Block{}    No           = m
choice No           m            = m

type MatchLit = Literal -> DeBruijnPattern -> Match [DeBruijnPattern]

noMatchLit :: MatchLit
noMatchLit _ _ = No

yesMatchLit :: MatchLit
yesMatchLit _ q@VarP{} = Yes [q]
yesMatchLit l (DotP t) = case buildPattern t of
  Just q  -> yesMatchLit l q
  Nothing -> No
yesMatchLit _ _          = No

-- | Check if a clause could match given generously chosen literals
matchLits :: Clause -> [Arg DeBruijnPattern] -> Bool
matchLits c ps =
  case matchClause yesMatchLit ps 0 c of
    Yes _ -> True
    _     -> False

-- | @matchClause mlit qs i c@ checks whether clause @c@ number @i@
--   covers a split clause with patterns @qs@.
matchClause :: MatchLit -> [Arg DeBruijnPattern] -> Nat -> Clause
            -> Match (Nat,[DeBruijnPattern])
matchClause mlit qs i c = (\q -> (i,q)) <$> matchPats mlit (clausePats c) qs

-- | @matchPats mlit ps qs@ checks whether a function clause with patterns
--   @ps@ covers a split clause with patterns @qs@.
--
--   Issue #842 / #1986: This is accepted:
--   @
--     F : Bool -> Set1
--     F true = Set
--     F      = \ x -> Set
--   @
--   For the second clause, the split clause is @F false@,
--   so there are more patterns in the split clause than
--   in the considered clause.  These additional patterns
--   are simply dropped by @zipWith@.  This will result
--   in @mconcat []@ which is @Yes []@.
matchPats :: MatchLit -> [Arg (Pattern' a)] -> [Arg DeBruijnPattern]
          -> Match [DeBruijnPattern]
matchPats mlit ps qs = mconcat $ [ projPatternsLeftInSplitClause ] ++
    zipWith (matchPat mlit) (map unArg ps) (map unArg qs) ++
    [ projPatternsLeftInMatchedClause ]
  where
    -- Andreas, 2016-06-03, issue #1986:
    -- catch-all for copatterns is inconsistent as found by Ulf.
    -- Thus, if the split clause has copatterns left,
    -- the current (shorter) clause is not considered covering.
    projPatternsLeftInSplitClause =
      let qsrest = map unArg $ drop (length ps) qs
      in  case mapMaybe isProjP qsrest of
            [] -> Yes [] -- no proj. patterns left
            _  -> No     -- proj. patterns left
    -- If the current clause has additional copatterns in
    -- comparison to the split clause, we should split on them.
    projPatternsLeftInMatchedClause =
      let psrest = map unArg $ drop (length qs) ps
      in  case mapMaybe isProjP psrest of
            [] -> Yes []               -- no proj. patterns left
            ds -> Block (Any True) []  -- proj. patterns left

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
--   that have to be instantiated (an projection names of copattern matches)
--   to make the split clause an instance of the function clause.
--
--   'BlockP' yields to 'Block', since blocking vars can also
--   block the result type.
instance Monoid a => Semigroup (Match a) where
  Yes a   <> Yes b   = Yes $ mappend a b
  Yes _   <> m       = m
  No      <> _       = No
  Block{} <> No      = No
  Block r xs <>
                 Block s ys = Block (mappend r s) $ mappend xs ys
  m@Block{} <> Yes{} = m

instance Monoid a => Monoid (Match a) where
  mempty = Yes mempty
  mappend = (<>)

-- | @matchPat mlit p q@ checks whether a function clause pattern @p@
--   covers a split clause pattern @q@.  There are three results:
--   @Yes rs@ means it covers, because @p@ is a variable pattern. @rs@ collects
--   the instantiations of the variables in @p@ s.t. @p[rs] = q@.
--   @No@ means it does not cover.
--   @Block [x]@ means @p@ is a proper instance of @q@ and could become
--   a cover if @q@ was split on variable @x@.
matchPat :: MatchLit -> Pattern' a -> DeBruijnPattern -> Match [DeBruijnPattern]
matchPat _    (VarP _) q = Yes [q]
matchPat _    (DotP _) q = Yes []
-- Jesper, 2014-11-04: putting 'Yes [q]' here triggers issue 1333.
-- Not checking for trivial patterns should be safe here, as dot patterns are
-- guaranteed to match if the rest of the pattern does, so some extra splitting
-- on them doesn't change the reduction behaviour.
matchPat mlit (LitP l) q = mlit l q
matchPat _    (ProjP _ d) (ProjP _ d') = if d == d' then Yes [] else No
matchPat _    (ProjP _ d) _ = __IMPOSSIBLE__
matchPat mlit p@(ConP c _ ps) q = case q of
  VarP x -> Block (Any False) [BlockingVar (dbPatVarIndex x) (Just [c])]
  ConP c' i qs
    | c == c'   -> matchPats mlit (map (fmap namedThing) ps) (map (fmap namedThing) qs)
    | otherwise -> No
  DotP t -> case buildPattern t of
    Just q  -> matchPat mlit p q
    Nothing -> No
  LitP _  -> __IMPOSSIBLE__
  ProjP{} -> __IMPOSSIBLE__
