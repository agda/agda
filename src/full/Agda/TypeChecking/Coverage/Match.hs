{-# LANGUAGE CPP           #-}

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

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Records
import Agda.TypeChecking.Substitute

import Agda.Utils.Permutation
import Agda.Utils.Size
import Agda.Utils.List
import Agda.Utils.Monad

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
match :: [Clause] -> [NamedArg DeBruijnPattern] -> Match (Nat,([DeBruijnPattern],[Literal]))
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
    matchIt i c = (i,) <$>
      matchClause yesMatchLit ps i c +++
      matchClause noMatchLit  ps i c

    Yes _     +++ m = m
    No        +++ _ = No
    m@Block{} +++ _ = m

-- | Convert the root of a term into a pattern constructor, if possible.
buildPattern :: Term -> Maybe DeBruijnPattern
buildPattern (Con c ci args) = Just $
  ConP c (toConPatternInfo ci) $ map (fmap $ unnamed . DotP) args
buildPattern (Var i [])     = Just $ deBruijnVar i
buildPattern (Shared p)     = buildPattern (derefPtr p)
buildPattern _              = Nothing

-- | A pattern that matches anything (modulo eta).
isTrivialPattern :: (HasConstInfo m) => Pattern' a -> m Bool
isTrivialPattern p = case p of
  VarP{}      -> return True
  DotP{}      -> return True
  AbsurdP{}   -> return True
  ConP c i ps -> andM $ (isEtaCon $ conName c)
                      : (map (isTrivialPattern . namedArg) ps)
  LitP{}      -> return False
  ProjP{}     -> return False

-- | If matching succeeds, we return the instantiation of the clause pattern vector
--   to obtain the split clause pattern vector, plus the literals of the clause patterns
--   matched against split clause variables.
type MatchResult = Match ([DeBruijnPattern],[Literal])

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

-- | Could the literal cover (an instantiation of) the split clause pattern?
--   Basically, the split clause pattern needs to be a variable.
--
--   Note: literal patterns do not occur in the split clause
--   since we cannot split into all possible literals (that would be infeasible).
type MatchLit = Literal -> DeBruijnPattern -> MatchResult

-- | Use this function if literal patterns should not cover a split clause pattern.
noMatchLit :: MatchLit
noMatchLit _ _ = No

-- | Use this function if a literal pattern should cover a split clause variable pattern.
yesMatchLit :: MatchLit
yesMatchLit l q@VarP{} = Yes ([q], [l])
yesMatchLit l (DotP t) = maybe No (yesMatchLit l) $ buildPattern t
yesMatchLit _ ConP{}   = No
yesMatchLit _ ProjP{}  = No
yesMatchLit _ AbsurdP{} = __IMPOSSIBLE__
yesMatchLit _ LitP{}   = __IMPOSSIBLE__

-- | Check if a clause could match given generously chosen literals
matchLits :: Clause -> [NamedArg DeBruijnPattern] -> Maybe [Literal]
matchLits c ps =
  case matchClause yesMatchLit ps 0 c of
    Yes (qs,ls) -> Just ls
    _ -> Nothing

-- | @matchClause mlit qs i c@ checks whether clause @c@ number @i@
--   covers a split clause with patterns @qs@.
matchClause
  :: MatchLit
     -- ^ Consider literals?
  -> [NamedArg DeBruijnPattern]
     -- ^ Split clause patterns @qs@.
  -> Nat
     -- ^ Clause number @i@.
  -> Clause
     -- ^ Clause @c@ to cover split clause.
  -> MatchResult
     -- ^ Result.
     --   If 'Yes' the instantiation @rs@ such that @(namedClausePats c)[rs] == qs@.
matchClause mlit qs i c = matchPats mlit (namedClausePats c) qs


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

matchPats
  :: MatchLit
     -- ^ Matcher for literals.
  -> [NamedArg (Pattern' a)]
     -- ^ Clause pattern vector @ps@ (to cover split clause pattern vector).
  -> [NamedArg DeBruijnPattern]
     -- ^ Split clause pattern vector @qs@ (to be covered by clause pattern vector).
  -> MatchResult
     -- ^ Result.
     --   If 'Yes' the instantiation @rs@ such that @ps[rs] == qs@.

matchPats mlit ps qs = mconcat $ [ projPatternsLeftInSplitClause ] ++
    zipWith (matchPat mlit) (map namedArg ps) (map namedArg qs) ++
    [ projPatternsLeftInMatchedClause ]
  where
    -- Patterns left in split clause:
    qsrest = drop (length ps) qs
    -- Andreas, 2016-06-03, issue #1986:
    -- catch-all for copatterns is inconsistent as found by Ulf.
    -- Thus, if the split clause has copatterns left,
    -- the current (shorter) clause is not considered covering.
    projPatternsLeftInSplitClause =
        case mapMaybe isProjP qsrest of
            [] -> mempty -- no proj. patterns left
            _  -> No     -- proj. patterns left

    -- Patterns left in candidate clause:
    psrest = drop (length qs) ps
    -- If the current clause has additional copatterns in
    -- comparison to the split clause, we should split on them.
    projPatternsLeftInMatchedClause =
        case mapMaybe isProjP psrest of
            [] -> mempty               -- no proj. patterns left
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

instance Semigroup a => Semigroup (Match a) where
  Yes a      <> Yes b      = Yes (a <> b)
  Yes _      <> m          = m
  No         <> _          = No
  Block{}    <> No         = No
  Block r xs <> Block s ys = Block (r <> s) (xs <> ys)
  m@Block{}  <> Yes{}      = m

instance (Semigroup a, Monoid a) => Monoid (Match a) where
  mempty  = Yes mempty
  mappend = (<>)


-- | @matchPat mlit p q@ checks whether a function clause pattern @p@
--   covers a split clause pattern @q@.  There are three results:
--   @Yes rs@ means it covers, because @p@ is a variable pattern. @rs@ collects
--   the instantiations of the variables in @p@ s.t. @p[rs] = q@.
--   @No@ means it does not cover.
--   @Block [x]@ means @p@ is a proper instance of @q@ and could become
--   a cover if @q@ was split on variable @x@.

matchPat
  :: MatchLit
     -- ^ Matcher for literals.
  -> Pattern' a
     -- ^ Clause pattern @p@ (to cover split clause pattern).
  -> DeBruijnPattern
     -- ^ Split clause pattern @q@ (to be covered by clause pattern).
  -> MatchResult
     -- ^ Result.
     --   If 'Yes', also the instantiation @rs@ of the clause pattern variables
     --   to produce the split clause pattern, @p[rs] = q@.

matchPat _    VarP{}   q = Yes ([q],[])
matchPat _    DotP{}   q = mempty
matchPat _    AbsurdP{} q = mempty
-- Jesper, 2014-11-04: putting 'Yes [q]' here triggers issue 1333.
-- Not checking for trivial patterns should be safe here, as dot patterns are
-- guaranteed to match if the rest of the pattern does, so some extra splitting
-- on them doesn't change the reduction behaviour.
matchPat mlit (LitP l) q = mlit l q
matchPat _    (ProjP _ d) (ProjP _ d') = if d == d' then mempty else No
matchPat _    ProjP{} _ = __IMPOSSIBLE__
matchPat mlit p@(ConP c _ ps) q = case q of
  VarP x -> Block (Any False) [BlockingVar (dbPatVarIndex x) (Just [c])]
  ConP c' i qs
    | c == c'   -> matchPats mlit ps qs
    | otherwise -> No
  DotP t  -> maybe No (matchPat mlit p) $ buildPattern t
  AbsurdP{} -> __IMPOSSIBLE__  -- excluded by typing
  LitP _  -> __IMPOSSIBLE__  -- split clause has no literal patterns
  ProjP{} -> __IMPOSSIBLE__  -- excluded by typing
