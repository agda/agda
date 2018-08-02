{-# LANGUAGE CPP           #-}

module Agda.TypeChecking.Coverage.Match where

import Control.Monad.State

import Prelude hiding ( null )

import qualified Data.List as List
import Data.Maybe (mapMaybe, isJust, fromMaybe)
import Data.Monoid ( Monoid, mempty, mappend, mconcat )
import Data.Semigroup ( Semigroup, (<>), Any(..) )
import Data.Traversable (traverse)

import Agda.Syntax.Abstract (IsProjP(..))
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern ()
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty ( PrettyTCM(..) )
import Agda.TypeChecking.Records
import Agda.TypeChecking.Substitute

import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty ( Pretty(..), text, (<+>), cat , prettyList_ )
import qualified Agda.Utils.Pretty as P
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
match :: [Clause] -> [NamedArg SplitPattern] -> Match (Nat,[SplitPattern])
match cs ps = foldr choice No $ zipWith matchIt [0..] cs
  where
    matchIt i c = (i,) <$> matchClause ps c

-- | For each variable in the patterns of a split clause, we remember the
--   de Bruijn-index and the literals excluded by previous matches.
data SplitPatVar = SplitPatVar
  { splitPatVarName   :: PatVarName
  , splitPatVarIndex  :: Int
  , splitExcludedLits :: [Literal]
  } deriving (Show)

instance Pretty SplitPatVar where
  prettyPrec _ x =
    (text $ patVarNameToString (splitPatVarName x)) P.<>
    (text $ "@" ++ show (splitPatVarIndex x)) P.<>
    (ifNull (splitExcludedLits x) empty $ \lits ->
      text "\\{" P.<> prettyList_ lits P.<> text "}")

instance PrettyTCM SplitPatVar where
  prettyTCM = prettyTCM . var . splitPatVarIndex

type SplitPattern = Pattern' SplitPatVar

toSplitVar :: DBPatVar -> SplitPatVar
toSplitVar x = SplitPatVar (dbPatVarName x) (dbPatVarIndex x) []

fromSplitVar :: SplitPatVar -> DBPatVar
fromSplitVar x = DBPatVar (splitPatVarName x) (splitPatVarIndex x)

instance DeBruijn SplitPatVar where
  deBruijnView x = deBruijnView (fromSplitVar x)
  debruijnNamedVar n i = toSplitVar (debruijnNamedVar n i)

toSplitPatterns :: [NamedArg DeBruijnPattern] -> [NamedArg SplitPattern]
toSplitPatterns = (fmap . fmap . fmap . fmap) toSplitVar

fromSplitPatterns :: [NamedArg SplitPattern] -> [NamedArg DeBruijnPattern]
fromSplitPatterns = (fmap . fmap . fmap . fmap) fromSplitVar

instance DeBruijn SplitPattern where
  debruijnNamedVar n i  = varP $ SplitPatVar n i []
  deBruijnView _        = Nothing

type SplitPSubstitution = Substitution' SplitPattern

toSplitPSubst :: PatternSubstitution -> SplitPSubstitution
toSplitPSubst = (fmap . fmap) toSplitVar

fromSplitPSubst :: SplitPSubstitution -> PatternSubstitution
fromSplitPSubst = (fmap . fmap) fromSplitVar

applySplitPSubst :: (Subst Term a) => SplitPSubstitution -> a -> a
applySplitPSubst = applyPatSubst . fromSplitPSubst

-- TODO: merge this instance and the one for DeBruijnPattern in
-- Substitute.hs into one for Subst (Pattern' a) (Pattern' a).
instance Subst SplitPattern SplitPattern where
  applySubst IdS p = p
  applySubst rho p = case p of
    VarP o x     ->
      usePatOrigin o $
      useName (splitPatVarName x) $
      useExcludedLits (splitExcludedLits x) $
      lookupS rho $ splitPatVarIndex x
    DotP o u     -> DotP o $ applySplitPSubst rho u
    ConP c ci ps -> ConP c ci $ applySubst rho ps
    DefP o q ps -> DefP o q $ applySubst rho ps
    LitP x       -> p
    ProjP{}      -> p
    IApplyP o _ _ x  ->
      usePatOrigin o $
      useName (splitPatVarName x) $
      useExcludedLits (splitExcludedLits x) $
      lookupS rho $ splitPatVarIndex x

    where
      useName :: PatVarName -> SplitPattern -> SplitPattern
      useName n (VarP o x)
        | isUnderscore (splitPatVarName x)
        = VarP o $ x { splitPatVarName = n }
      useName _ x = x

      useExcludedLits :: [Literal] -> SplitPattern -> SplitPattern
      useExcludedLits lits = \case
        (VarP o x) -> VarP o $ x
          { splitExcludedLits = lits ++ splitExcludedLits x }
        p -> p


-- | A pattern that matches anything (modulo eta).
isTrivialPattern :: (HasConstInfo m) => Pattern' a -> m Bool
isTrivialPattern p = case p of
  VarP{}      -> return True
  DotP{}      -> return True
  ConP c i ps -> andM $ (isEtaCon $ conName c)
                      : (map (isTrivialPattern . namedArg) ps)
  DefP{}      -> return False
  LitP{}      -> return False
  ProjP{}     -> return False
  IApplyP{}   -> return True

-- | If matching succeeds, we return the instantiation of the clause pattern vector
--   to obtain the split clause pattern vector.
type MatchResult = Match [SplitPattern]

-- | If matching is inconclusive (@Block@) we want to know which
--   variables are blocking the match.
data Match a
  = Yes a   -- ^ Matches unconditionally.
  | No      -- ^ Definitely does not match.
  | Block
    { blockedOnResult :: Bool
      -- ^ True if the clause has a result split
    , blockedOnVars :: BlockingVars
      -- ^ @BlockingVar i cs ls o@ means variable @i@ is blocked on
      -- constructors @cs@ and literals @ls@.
    }
  deriving (Functor)

-- | Variable blocking a match.
data BlockingVar = BlockingVar
  { blockingVarNo  :: Nat
    -- ^ De Bruijn index of variable blocking the match.
  , blockingVarCons :: [ConHead]
    -- ^ Constructors in this position.
  , blockingVarLits :: [Literal]
    -- ^ Literals in this position.
  , blockingVarOverlap :: Bool
    -- ^ True if at least one clause has a variable pattern in this
    --   position.
  } deriving (Show)

instance Pretty BlockingVar where
  pretty (BlockingVar i cs ls o) = cat
    [ text ("variable " ++ show i)
    , if null cs then empty else text " blocked on constructors" <+> pretty cs
    , if null ls then empty else text " blocked on literals" <+> pretty ls
    , if o then text " (overlapping)" else empty
    ]

type BlockingVars = [BlockingVar]

blockedOnConstructor :: Nat -> ConHead -> Match a
blockedOnConstructor i c = Block False [BlockingVar i [c] [] False]

blockedOnLiteral :: Nat -> Literal -> Match a
blockedOnLiteral i l = Block False [BlockingVar i [] [l] False]

blockedOnProjection :: Match a
blockedOnProjection = Block True []

-- | Lens for 'blockingVarCons'.
mapBlockingVarCons :: ([ConHead] -> [ConHead]) -> BlockingVar -> BlockingVar
mapBlockingVarCons f b = b { blockingVarCons = f (blockingVarCons b) }

-- | Lens for 'blockingVarLits'.
mapBlockingVarLits :: ([Literal] -> [Literal]) -> BlockingVar -> BlockingVar
mapBlockingVarLits f b = b { blockingVarLits = f (blockingVarLits b) }

setBlockingVarOverlap :: BlockingVar -> BlockingVar
setBlockingVarOverlap = \x -> x { blockingVarOverlap = True }

overlapping :: BlockingVars -> BlockingVars
overlapping = map setBlockingVarOverlap

-- | Left dominant merge of blocking vars.
zipBlockingVars :: BlockingVars -> BlockingVars -> BlockingVars
zipBlockingVars xs ys = map upd xs
  where
    upd (BlockingVar x cons lits o) = case List.find ((x ==) . blockingVarNo) ys of
      Just (BlockingVar _ cons' lits' o') -> BlockingVar x (cons ++ cons') (lits ++ lits') (o || o')
      Nothing -> BlockingVar x cons lits True

-- | @choice m m'@ combines the match results @m@ of a function clause
--   with the (already combined) match results $m'$ of the later clauses.
--   It is for skipping clauses that definitely do not match ('No').
--   It is left-strict, to be used with @foldr@.
--   If one clause unconditionally matches ('Yes') we do not look further.
choice :: Match a -> Match a -> Match a
choice (Yes a)      _            = Yes a
choice (Block r xs) (Block s ys) = Block (r && s) $ zipBlockingVars xs ys
choice (Block r xs) (Yes _)      = Block r $ overlapping xs
choice m@Block{}    No           = m
choice No           m            = m

-- | @matchClause qs i c@ checks whether clause @c@
--   covers a split clause with patterns @qs@.
matchClause
  :: [NamedArg SplitPattern]
     -- ^ Split clause patterns @qs@.
  -> Clause
     -- ^ Clause @c@ to cover split clause.
  -> MatchResult
     -- ^ Result.
     --   If 'Yes' the instantiation @rs@ such that @(namedClausePats c)[rs] == qs@.
matchClause qs c = matchPats (namedClausePats c) qs


-- | @matchPats ps qs@ checks whether a function clause with patterns
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
  :: [NamedArg (Pattern' a)]
     -- ^ Clause pattern vector @ps@ (to cover split clause pattern vector).
  -> [NamedArg SplitPattern]
     -- ^ Split clause pattern vector @qs@ (to be covered by clause pattern vector).
  -> MatchResult
     -- ^ Result.
     --   If 'Yes' the instantiation @rs@ such that @ps[rs] == qs@.

matchPats ps qs = mconcat $ [ projPatternsLeftInSplitClause ] ++
    zipWith matchPat (map namedArg ps) (map namedArg qs) ++
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
            ds -> blockedOnProjection  -- proj. patterns left


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
  Block r xs <> Block s ys = Block (r || s) (xs ++ ys)
  m@Block{}  <> Yes{}      = m

instance (Semigroup a, Monoid a) => Monoid (Match a) where
  mempty  = Yes mempty
  mappend = (<>)


-- | @matchPat p q@ checks whether a function clause pattern @p@
--   covers a split clause pattern @q@.  There are three results:
--   @Yes rs@ means it covers, because @p@ is a variable pattern. @rs@ collects
--   the instantiations of the variables in @p@ s.t. @p[rs] = q@.
--   @No@ means it does not cover.
--   @Block [x]@ means @p@ is a proper instance of @q@ and could become
--   a cover if @q@ was split on variable @x@.
--   @BlockLit [x] means @p@ is a proper instance of @q@ and could become
--   a cover if variable @x@ is instantiated with an appropriate literal.

matchPat
  :: Pattern' a
     -- ^ Clause pattern @p@ (to cover split clause pattern).
  -> SplitPattern
     -- ^ Split clause pattern @q@ (to be covered by clause pattern).
  -> MatchResult
     -- ^ Result.
     --   If 'Yes', also the instantiation @rs@ of the clause pattern variables
     --   to produce the split clause pattern, @p[rs] = q@.

matchPat VarP{}   q = Yes [q]
matchPat DotP{}   q = mempty
-- Jesper, 2014-11-04: putting 'Yes [q]' here triggers issue 1333.
-- Not checking for trivial patterns should be safe here, as dot patterns are
-- guaranteed to match if the rest of the pattern does, so some extra splitting
-- on them doesn't change the reduction behaviour.
matchPat p@(LitP l) q = case q of
  VarP _ x -> if l `elem` splitExcludedLits x
              then No
              else blockedOnLiteral (splitPatVarIndex x) l
  ConP{}   -> No
  DotP{}   -> No
  LitP l'  -> if l == l' then Yes [] else No
  DefP{}   -> No
  ProjP{}  -> __IMPOSSIBLE__  -- excluded by typing
  IApplyP{} -> __IMPOSSIBLE__
matchPat (ProjP _ d) (ProjP _ d') = if d == d' then mempty else No
matchPat ProjP{} _ = __IMPOSSIBLE__
matchPat IApplyP{} q = Yes [q]
matchPat p@(ConP c _ ps) q = case q of
  VarP _ x -> blockedOnConstructor (splitPatVarIndex x) c
  ConP c' i qs
    | c == c'   -> matchPats ps qs
    | otherwise -> No
  DotP o t  -> No
  LitP _    -> No
  DefP{}   -> No
  ProjP{}   -> __IMPOSSIBLE__  -- excluded by typing
  IApplyP _ _ _ x -> blockedOnConstructor (splitPatVarIndex x) c
matchPat (DefP o c ps) q = case q of
  VarP _ x -> __IMPOSSIBLE__ -- blockedOnConstructor (splitPatVarIndex x) c
  ConP c' i qs -> No
  DotP o t  -> No
  LitP _    -> No
  DefP o c' qs
    | c == c'   -> matchPats ps qs
    | otherwise -> No
  ProjP{}   -> __IMPOSSIBLE__  -- excluded by typing
  IApplyP _ _ _ x -> __IMPOSSIBLE__ --blockedOnConstructor (splitPatVarIndex x) c
