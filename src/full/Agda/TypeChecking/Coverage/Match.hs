{-# LANGUAGE CPP           #-}

module Agda.TypeChecking.Coverage.Match
  ( Match(..), match
  , SplitPattern, SplitPatVar(..), fromSplitPatterns, toSplitPatterns
  , toSplitPSubst, applySplitPSubst
  , isTrivialPattern
  , BlockingVar(..), BlockingVars, BlockedOnResult(..)
  , setBlockingVarOverlap
  , ApplyOrIApply(..)
  ) where

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
import Agda.Syntax.Position

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Pretty ( PrettyTCM(..) )
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
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

type SplitAssignment = (Nat,SplitPattern)

-- | Match the given patterns against a list of clauses
match :: (MonadReduce m , HasConstInfo m , HasBuiltins m) => [Clause] -> [NamedArg SplitPattern] -> m (Match (Nat,[SplitAssignment]))
match cs ps = foldr choice (return No) $ zipWith matchIt [0..] cs
  where
    matchIt :: (MonadReduce m , HasConstInfo m , HasBuiltins m) => Nat -> Clause -> m (Match (Nat,[SplitAssignment]))
    matchIt i c = fmap (i,) <$> matchClause ps c

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
      "\\{" P.<> prettyList_ lits P.<> "}")

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
    IApplyP o l r x  ->
      useEndPoints (applySplitPSubst rho l) (applySplitPSubst rho r) $
      usePatOrigin o $
      useName (splitPatVarName x) $
      useExcludedLits (splitExcludedLits x) $
      lookupS rho $ splitPatVarIndex x

    where
      -- see Subst for DeBruijnPattern
      useEndPoints :: Term -> Term -> SplitPattern -> SplitPattern
      useEndPoints l r (VarP o x)        = IApplyP o l r x
      useEndPoints l r (IApplyP o _ _ x) = IApplyP o l r x
      useEndPoints l r x                 = __IMPOSSIBLE__

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
type MatchResult = Match [SplitAssignment]

-- | If matching is inconclusive (@Block@) we want to know which
--   variables or projections are blocking the match.
data Match a
  = Yes a   -- ^ Matches unconditionally.
  | No      -- ^ Definitely does not match.
  | Block
    { blockedOnResult :: BlockedOnResult
      -- ^ @BlockedOnProj o@ if the clause has a result split
    , blockedOnVars :: BlockingVars
      -- ^ @BlockingVar i cs ls o@ means variable @i@ is blocked on
      -- constructors @cs@ and literals @ls@.
    }
  deriving (Functor)

data ApplyOrIApply = IsApply | IsIApply

data BlockedOnResult
  = BlockedOnProj      -- ^ Blocked on unsplit projection
     { blockedOnResultOverlap :: Bool
       -- ^ True if there are also matching clauses without an unsplit
       -- copattern.
     }
  | BlockedOnApply     -- ^ Blocked on unintroduced argument
     { blockedOnResultIApply :: ApplyOrIApply
       -- ^ True if the unintroduced argument was an IApply pattern
     }
  | NotBlockedOnResult

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
    , if null cs then empty else " blocked on constructors" <+> pretty cs
    , if null ls then empty else " blocked on literals" <+> pretty ls
    , if o then " (overlapping)" else empty
    ]

type BlockingVars = [BlockingVar]

yes :: Monad m => a -> m (Match a)
yes = return . Yes

no :: Monad m => m (Match a)
no = return No

blockedOnConstructor :: Monad m => Nat -> ConHead -> m (Match a)
blockedOnConstructor i c = return $ Block NotBlockedOnResult [BlockingVar i [c] [] False]

blockedOnLiteral :: Monad m => Nat -> Literal -> m (Match a)
blockedOnLiteral i l = return $ Block NotBlockedOnResult [BlockingVar i [] [l] False]

blockedOnProjection :: Monad m => m (Match a)
blockedOnProjection = return $ Block (BlockedOnProj False) []

blockedOnApplication :: Monad m => ApplyOrIApply -> m (Match a)
blockedOnApplication b = return $ Block (BlockedOnApply b) []

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

setBlockedOnResultOverlap :: BlockedOnResult -> BlockedOnResult
setBlockedOnResultOverlap b = case b of
  BlockedOnProj{}      -> b { blockedOnResultOverlap = True }
  BlockedOnApply{}     -> b
  NotBlockedOnResult{} -> b

anyBlockedOnResult :: BlockedOnResult -> BlockedOnResult -> BlockedOnResult
anyBlockedOnResult b1 b2 = case (b1,b2) of
  (NotBlockedOnResult , b2                ) -> b2
  (b1                 , NotBlockedOnResult) -> b1
  (_                  , _                 ) -> __IMPOSSIBLE__

-- | Left dominant merge of `BlockedOnResult`.
choiceBlockedOnResult :: BlockedOnResult -> BlockedOnResult -> BlockedOnResult
choiceBlockedOnResult b1 b2 = case (b1,b2) of
  (NotBlockedOnResult  , _                 ) -> NotBlockedOnResult
  (BlockedOnProj _     , NotBlockedOnResult) -> BlockedOnProj True
  (BlockedOnProj o1    , BlockedOnProj o2  ) -> BlockedOnProj (o1 || o2)
  (BlockedOnProj o1    , BlockedOnApply{}  ) -> BlockedOnProj True
  (BlockedOnApply b    , _                 ) -> BlockedOnApply b

-- | @choice m m'@ combines the match results @m@ of a function clause
--   with the (already combined) match results $m'$ of the later clauses.
--   It is for skipping clauses that definitely do not match ('No').
--   It is left-strict, to be used with @foldr@.
--   If one clause unconditionally matches ('Yes') we do not look further.
choice :: Monad m => m (Match a) -> m (Match a) -> m (Match a)
choice m m' = m >>= \case
  Yes a -> yes a
  Block r xs -> m' >>= \case
    Block s ys -> return $ Block (choiceBlockedOnResult r s) $ zipBlockingVars xs ys
    Yes _      -> return $ Block (setBlockedOnResultOverlap r) $ overlapping xs
    No         -> return $ Block r xs
  No    -> m'

-- | @matchClause qs i c@ checks whether clause @c@
--   covers a split clause with patterns @qs@.
matchClause
  :: (MonadReduce m , HasConstInfo m , HasBuiltins m)
  => [NamedArg SplitPattern]
     -- ^ Split clause patterns @qs@.
  -> Clause
     -- ^ Clause @c@ to cover split clause.
  -> m MatchResult
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
  :: (MonadReduce m , HasConstInfo m , HasBuiltins m, DeBruijn a)
  => [NamedArg (Pattern' a)]
     -- ^ Clause pattern vector @ps@ (to cover split clause pattern vector).
  -> [NamedArg SplitPattern]
     -- ^ Split clause pattern vector @qs@ (to be covered by clause pattern vector).
  -> m MatchResult
     -- ^ Result.
     --   If 'Yes' the instantiation @rs@ such that @ps[rs] == qs@.
matchPats [] [] = yes []
matchPats (p:ps) (q:qs) =
  matchPat (namedArg p) (namedArg q) `combine` matchPats ps qs

-- Patterns left in split clause:
-- Andreas, 2016-06-03, issue #1986:
-- catch-all for copatterns is inconsistent as found by Ulf.
-- Thus, if the split clause has copatterns left,
-- the current (shorter) clause is not considered covering.
matchPats [] qs@(_:_) = case mapMaybe isProjP qs of
  [] -> yes [] -- no proj. patterns left
  _  -> no     -- proj. patterns left

-- Patterns left in candidate clause:
-- If the current clause has additional copatterns in
-- comparison to the split clause, we should split on them.
matchPats (p:ps) [] = case isProjP p of
  Just{}  -> blockedOnProjection
  Nothing -> blockedOnApplication (case namedArg p of IApplyP{} -> IsIApply; _ -> IsApply)

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
combine :: (Monad m, Semigroup a) => m (Match a) -> m (Match a) -> m (Match a)
combine m m' = m >>= \case
    Yes a -> m' >>= \case
      Yes b -> yes (a <> b)
      y     -> return y
    No    -> no
    x@(Block r xs) -> m' >>= \case
      No    -> no
      Block s ys -> return $ Block (anyBlockedOnResult r s) (xs ++ ys)
      Yes{} -> return x

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
  :: (MonadReduce m , HasConstInfo m , HasBuiltins m, DeBruijn a)
  => Pattern' a
     -- ^ Clause pattern @p@ (to cover split clause pattern).
  -> SplitPattern
     -- ^ Split clause pattern @q@ (to be covered by clause pattern).
  -> m MatchResult
     -- ^ Result.
     --   If 'Yes', also the instantiation @rs@ of the clause pattern variables
     --   to produce the split clause pattern, @p[rs] = q@.
matchPat p q = case p of
  VarP _ x   -> yes [(fromMaybe __IMPOSSIBLE__ (deBruijnView x),q)]
  DotP{}   -> yes []
  -- Jesper, 2014-11-04: putting 'Yes [q]' here triggers issue 1333.
  -- Not checking for trivial patterns should be safe here, as dot patterns are
  -- guaranteed to match if the rest of the pattern does, so some extra splitting
  -- on them doesn't change the reduction behaviour.
  p@(LitP l) -> case q of
    VarP _ x -> if l `elem` splitExcludedLits x
                then no
                else blockedOnLiteral (splitPatVarIndex x) l
    _ -> isLitP q >>= \case
      Just l' -> if l == l' then yes [] else no
      Nothing -> no
  ProjP _ d -> case q of
    ProjP _ d' -> do
      d <- getOriginalProjection d
      if d == d' then yes [] else no
    _          -> __IMPOSSIBLE__
  IApplyP _ _ _ x -> yes [(fromMaybe __IMPOSSIBLE__ (deBruijnView x),q)]
  ConP c _ ps -> unDotP q >>= \case
    VarP _ x -> blockedOnConstructor (splitPatVarIndex x) c
    ConP c' i qs
      | c == c'   -> matchPats ps qs
      | otherwise -> no
    DotP o t  -> no
    LitP l    -> isLitP p >>= \case
      Just l' -> if l == l' then yes [] else no
      Nothing -> no
    DefP{}   -> no
    ProjP{}   -> __IMPOSSIBLE__  -- excluded by typing
    IApplyP _ _ _ x -> blockedOnConstructor (splitPatVarIndex x) c
  (DefP o c ps) -> unDotP q >>= \case
    VarP _ x -> __IMPOSSIBLE__ -- blockedOnConstructor (splitPatVarIndex x) c
    ConP c' i qs -> no
    DotP o t  -> no
    LitP _    -> no
    DefP o c' qs
      | c == c'   -> matchPats ps qs
      | otherwise -> no
    ProjP{}   -> __IMPOSSIBLE__  -- excluded by typing
    IApplyP _ _ _ x -> __IMPOSSIBLE__ --blockedOnConstructor (splitPatVarIndex x) c

-- unfold one level of a dot pattern to a proper pattern if possible
unDotP :: (MonadReduce m, DeBruijn (Pattern' a)) => Pattern' a -> m (Pattern' a)
unDotP (DotP o v) = reduce v >>= \case
  Var i [] -> return $ deBruijnVar i
  Con c _ vs -> do
    let ps = map (fmap $ unnamed . DotP o) $ fromMaybe __IMPOSSIBLE__ $ allApplyElims vs
    return $ ConP c noConPatternInfo ps
  Lit l -> return $ LitP l
  v     -> return $ dotP v
unDotP p = return p

isLitP :: (MonadReduce m, HasBuiltins m) => Pattern' a -> m (Maybe Literal)
isLitP (LitP l) = return $ Just l
isLitP (DotP _ u) = reduce u >>= \case
  Lit l -> return $ Just l
  _     -> return $ Nothing
isLitP (ConP c ci []) = do
  Con zero _ [] <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinZero
  if | c == zero -> return $ Just $ LitNat (getRange c) 0
     | otherwise -> return Nothing
isLitP (ConP c ci [a]) | visible a && isRelevant a = do
  Con suc _ [] <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinSuc
  if | c == suc  -> fmap inc <$> isLitP (namedArg a)
     | otherwise -> return Nothing
  where
    inc :: Literal -> Literal
    inc (LitNat r n) = LitNat (fuseRange c r) $ n + 1
    inc _ = __IMPOSSIBLE__
isLitP _ = return Nothing
