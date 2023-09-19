
{-| Given

    1. the function clauses @cs@
    2. the patterns @ps@ of the split clause

we want to compute a variable index (in the split clause) to split on next.

The matcher here checks whether the split clause is covered by one of
the given clauses @cs@ or whether further splitting is needed (and
when yes, where).
-}

module Agda.TypeChecking.Coverage.Match
  ( Match(..), match, matchClause
  , SplitPattern, SplitPatVar(..)
  , fromSplitPattern, fromSplitPatterns, toSplitPatterns
  , toSplitPSubst, applySplitPSubst
  , isTrivialPattern
  , BlockingVar(..), BlockingVars, BlockedOnResult(..)
  , setBlockingVarOverlap
  , ApplyOrIApply(..)
  ) where

import Prelude hiding ( null )

import Data.DList (DList)
import Data.Foldable (toList)
import qualified Data.List as List
import Data.Maybe (mapMaybe, fromMaybe)
import Data.Semigroup ( Semigroup, (<>))

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty ( PrettyTCM(..) )
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Utils.Null
import Agda.Syntax.Common.Pretty ( Pretty(..), text, (<+>), cat , prettyList_ )
import Agda.Utils.Monad
import Agda.Utils.Singleton

import Agda.Utils.Impossible

-- | If matching is inconclusive (@Block@) we want to know which
--   variables or projections are blocking the match.
data Match a
  = Yes a   -- ^ Matches unconditionally.
  | No      -- ^ Definitely does not match.
  | Block
    { blockedOnResult :: BlockedOnResult
      -- ^ @BlockedOnProj o@ if the clause has a result split.
    , blockedOnVars :: BlockingVars
      -- ^ @BlockingVar i cs ls o@ means variable @i@ is blocked on
      -- constructors @cs@ and literals @ls@.
    }
  deriving (Functor)

-- | Missing elimination blocking a match.
data BlockedOnResult
  = BlockedOnProj      -- ^ Blocked on unsplit projection.
     { blockedOnResultOverlap :: Bool
       -- ^ True if there are also matching clauses without an unsplit
       -- copattern.
     }
  | BlockedOnApply     -- ^ Blocked on unintroduced argument.
     { blockedOnResultIApply :: ApplyOrIApply
       -- ^ Is the unintroduced argument an 'IApply' pattern?
     }
  | NotBlockedOnResult

data ApplyOrIApply = IsApply | IsIApply

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
  , blockingVarLazy :: Bool
    -- ^ True if at least one clause has a lazy pattern in this position.
  } deriving (Show)

type BlockingVars = [BlockingVar]

-- | Substitution of 'SplitPattern's for de Bruijn indices in covering
--   clause to match 'SplitClause'.
type SplitInstantiation = [(Nat,SplitPattern)]

{-# SPECIALIZE match :: [Clause] -> [NamedArg SplitPattern] -> TCM (Match (Nat, SplitInstantiation)) #-}
-- | Match the given patterns against a list of clauses.
--
-- If successful, return the index of the covering clause.
--
match :: PureTCM m
      => [Clause]                           -- ^ Search for clause that covers the patterns.
      -> [NamedArg SplitPattern]            -- ^ Patterns of the current 'SplitClause'.
      -> m (Match (Nat, SplitInstantiation))
match cs ps = foldr choice (return No) $ zipWith matchIt [0..] cs
  where
    matchIt :: PureTCM m
            => Nat  -- Clause number.
            -> Clause
            -> m (Match (Nat, SplitInstantiation))
    matchIt i c = fmap (\s -> (i, toList s)) <$> matchClause ps c

-- | For each variable in the patterns of a split clause, we remember the
--   de Bruijn-index and the literals excluded by previous matches.

--  (See issue #708.)
data SplitPatVar = SplitPatVar
  { splitPatVarName   :: PatVarName
  , splitPatVarIndex  :: Int
  , splitExcludedLits :: [Literal]
  } deriving (Show)

instance Pretty SplitPatVar where
  prettyPrec _ x =
    text (patVarNameToString (splitPatVarName x)) <>
    text ("@" ++ show (splitPatVarIndex x)) <>
    ifNull (splitExcludedLits x) empty (\lits ->
      "\\{" <> prettyList_ lits <> "}")

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

fromSplitPattern :: NamedArg SplitPattern -> NamedArg DeBruijnPattern
fromSplitPattern = (fmap . fmap . fmap) fromSplitVar

fromSplitPatterns :: [NamedArg SplitPattern] -> [NamedArg DeBruijnPattern]
fromSplitPatterns = fmap fromSplitPattern

type SplitPSubstitution = Substitution' SplitPattern

toSplitPSubst :: PatternSubstitution -> SplitPSubstitution
toSplitPSubst = (fmap . fmap) toSplitVar

fromSplitPSubst :: SplitPSubstitution -> PatternSubstitution
fromSplitPSubst = (fmap . fmap) fromSplitVar

applySplitPSubst :: TermSubst a => SplitPSubstitution -> a -> a
applySplitPSubst = applyPatSubst . fromSplitPSubst

-- TODO: merge this instance and the one for DeBruijnPattern in
-- Substitute.hs into one for Subst (Pattern' a) (Pattern' a).
instance Subst SplitPattern where
  type SubstArg SplitPattern = SplitPattern

  applySubst IdS = id
  applySubst rho = \case
    VarP i x        ->
      usePatternInfo i $
      useName (splitPatVarName x) $
      useExcludedLits (splitExcludedLits x) $
      lookupS rho $ splitPatVarIndex x
    DotP i u        -> DotP i $ applySplitPSubst rho u
    ConP c ci ps    -> ConP c ci $ applySubst rho ps
    DefP i q ps     -> DefP i q $ applySubst rho ps
    p@LitP{}        -> p
    p@ProjP{}       -> p
    IApplyP i l r x ->
      useEndPoints (applySplitPSubst rho l) (applySplitPSubst rho r) $
      usePatternInfo i $
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


{-# SPECIALIZE isTrivialPattern :: Pattern' a -> TCM Bool #-}
-- | A pattern that matches anything (modulo eta).
isTrivialPattern :: (HasConstInfo m) => Pattern' a -> m Bool
isTrivialPattern = \case
  VarP{}      -> return True
  DotP{}      -> return True
  ConP c i ps -> andM $ ((conPLazy i ||) <$> isEtaCon (conName c))
                      : (map (isTrivialPattern . namedArg) ps)
  DefP{}      -> return False
  LitP{}      -> return False
  ProjP{}     -> return False
  IApplyP{}   -> return True

-- | If matching succeeds, we return the instantiation of the clause pattern vector
--   to obtain the split clause pattern vector.
type MatchResult = Match (DList (Nat, SplitPattern))

instance Pretty BlockingVar where
  pretty (BlockingVar i cs ls o l) = cat
    [ text ("variable " ++ show i)
    , if null cs then empty else " blocked on constructors" <+> pretty cs
    , if null ls then empty else " blocked on literals" <+> pretty ls
    , if o then " (overlapping)" else empty
    , if l then " (lazy)" else empty
    ]

yes :: Monad m => a -> m (Match a)
yes = return . Yes

no :: Monad m => m (Match a)
no = return No

blockedOnConstructor :: Monad m => Nat -> ConHead -> ConPatternInfo -> m (Match a)
blockedOnConstructor i c ci = return $ Block NotBlockedOnResult [BlockingVar i [c] [] False $ conPLazy ci]

blockedOnLiteral :: Monad m => Nat -> Literal -> m (Match a)
blockedOnLiteral i l = return $ Block NotBlockedOnResult [BlockingVar i [] [l] False False]

blockedOnProjection :: Monad m => m (Match a)
blockedOnProjection = return $ Block (BlockedOnProj False) []

blockedOnApplication :: Monad m => ApplyOrIApply -> m (Match a)
blockedOnApplication b = return $ Block (BlockedOnApply b) []
--UNUSED Liang-Ting Chen 2019-07-16
---- | Lens for 'blockingVarCons'.
--mapBlockingVarCons :: ([ConHead] -> [ConHead]) -> BlockingVar -> BlockingVar
--mapBlockingVarCons f b = b { blockingVarCons = f (blockingVarCons b) }
--
---- | Lens for 'blockingVarLits'.
--mapBlockingVarLits :: ([Literal] -> [Literal]) -> BlockingVar -> BlockingVar
--mapBlockingVarLits f b = b { blockingVarLits = f (blockingVarLits b) }

setBlockingVarOverlap :: BlockingVar -> BlockingVar
setBlockingVarOverlap = \x -> x { blockingVarOverlap = True }

overlapping :: BlockingVars -> BlockingVars
overlapping = map setBlockingVarOverlap

-- | Left dominant merge of blocking vars.
zipBlockingVars :: BlockingVars -> BlockingVars -> BlockingVars
zipBlockingVars xs ys = map upd xs
  where
    upd (BlockingVar x cons lits o l) = case List.find ((x ==) . blockingVarNo) ys of
      Just (BlockingVar _ cons' lits' o' l') -> BlockingVar x (cons ++ cons') (lits ++ lits') (o || o') (l || l')
      Nothing -> BlockingVar x cons lits True l

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
  (BlockedOnProj o1    , BlockedOnProj o2  ) -> BlockedOnProj (o1 || o2)
  (BlockedOnProj _     , _                 ) -> BlockedOnProj True
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

{-# SPECIALIZE matchClause :: [NamedArg SplitPattern] -> Clause -> TCM MatchResult #-}
matchClause
  :: PureTCM m
  => [NamedArg SplitPattern]
     -- ^ Split clause patterns @qs@.
  -> Clause
     -- ^ Clause @c@ to cover split clause.
  -> m MatchResult
     -- ^ Result.
     --   If 'Yes' the instantiation @rs@ such that @(namedClausePats c)[rs] == qs@.
matchClause qs c = matchPats (namedClausePats c) qs

{-# SPECIALIZE matchPats :: DeBruijn a => [NamedArg (Pattern' a)] -> [NamedArg SplitPattern] -> TCM MatchResult #-}
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
  :: (PureTCM m, DeBruijn a)
  => [NamedArg (Pattern' a)]
     -- ^ Clause pattern vector @ps@ (to cover split clause pattern vector).
  -> [NamedArg SplitPattern]
     -- ^ Split clause pattern vector @qs@ (to be covered by clause pattern vector).
  -> m MatchResult
     -- ^ Result.
     --   If 'Yes' the instantiation @rs@ such that @ps[rs] == qs@.
matchPats [] [] = yes mempty
matchPats (p:ps) (q:qs) =
  matchPat (namedArg p) (namedArg q) `combine` matchPats ps qs

-- Patterns left in split clause:
-- Andreas, 2016-06-03, issue #1986:
-- catch-all for copatterns is inconsistent as found by Ulf.
-- Thus, if the split clause has copatterns left,
-- the current (shorter) clause is not considered covering.
matchPats [] qs@(_:_) = case mapMaybe isProjP qs of
  [] -> yes mempty -- no proj. patterns left
  _  -> no         -- proj. patterns left

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

{-# SPECIALIZE matchPat :: DeBruijn a => Pattern' a -> SplitPattern -> TCM MatchResult #-}
-- | @matchPat p q@ checks whether a function clause pattern @p@
--   covers a split clause pattern @q@.  There are three results:
--
--   1. @Yes rs@ means it covers, because @p@ is a variable pattern. @rs@ collects
--      the instantiations of the variables in @p@ s.t. @p[rs] = q@.
--
--   2. @No@ means it does not cover.
--
--   3. @Block [x]@ means @p@ is a proper instance of @q@ and could become
--      a cover if @q@ was split on variable @x@.

matchPat
  :: (PureTCM m, DeBruijn a)
  => Pattern' a
     -- ^ Clause pattern @p@ (to cover split clause pattern).
  -> SplitPattern
     -- ^ Split clause pattern @q@ (to be covered by clause pattern).
  -> m MatchResult
     -- ^ Result.
     --   If 'Yes', also the instantiation @rs@ of the clause pattern variables
     --   to produce the split clause pattern, @p[rs] = q@.
matchPat p q = case p of

  VarP _ x ->
    yes $ singleton (fromMaybe __IMPOSSIBLE__ (deBruijnView x), q)

  DotP{} -> yes mempty
  -- Jesper, 2014-11-04: putting 'Yes [q]' here triggers issue 1333.
  -- Not checking for trivial patterns should be safe here, as dot patterns are
  -- guaranteed to match if the rest of the pattern does, so some extra splitting
  -- on them doesn't change the reduction behaviour.

  p@(LitP _ l) -> case q of
    VarP _ x -> if l `elem` splitExcludedLits x
                then no
                else blockedOnLiteral (splitPatVarIndex x) l
    _ -> isLitP q >>= \case
      Just l' -> if l == l' then yes mempty else no
      Nothing -> no

  ProjP _ d -> case q of
    ProjP _ d' -> do
      d <- getOriginalProjection d
      if d == d' then yes mempty else no
    _          -> __IMPOSSIBLE__

  IApplyP _ _ _ x ->
    yes $ singleton (fromMaybe __IMPOSSIBLE__ (deBruijnView x), q)

                           --    Issue #4179: If the inferred pattern is a literal
                           -- v  we need to turn it into a constructor pattern.
  ConP c ci ps -> unDotP q >>= unLitP >>= \case
    VarP _ x -> blockedOnConstructor (splitPatVarIndex x) c ci
    ConP c' i qs
      | c == c'   -> matchPats ps qs
      | otherwise -> no
    DotP o t  -> no
    DefP{}   -> no
    LitP{}    -> __IMPOSSIBLE__  -- excluded by typing and unLitP
    ProjP{}   -> __IMPOSSIBLE__  -- excluded by typing
    IApplyP _ _ _ x -> blockedOnConstructor (splitPatVarIndex x) c ci

  DefP o c ps -> unDotP q >>= \case
    VarP _ x -> no
    ConP c' i qs -> no
    DotP o t  -> no
    LitP{}    -> no
    DefP o c' qs
      | c == c'   -> matchPats ps qs
      | otherwise -> no
    ProjP{}   -> __IMPOSSIBLE__  -- excluded by typing
    IApplyP _ _ _ x -> __IMPOSSIBLE__ -- blockedOnConstructor (splitPatVarIndex x) c

{-# SPECIALIZE unDotP :: DeBruijn a => Pattern' a -> TCM (Pattern' a) #-}
-- | Unfold one level of a dot pattern to a proper pattern if possible.
unDotP :: (MonadReduce m, DeBruijn a) => Pattern' a -> m (Pattern' a)
unDotP (DotP o v) = reduce v >>= \case
  Var i [] -> return $ deBruijnVar i
  Con c _ vs -> do
    let ps = map (fmap $ unnamed . DotP o) $ fromMaybe __IMPOSSIBLE__ $ allApplyElims vs
    return $ ConP c noConPatternInfo ps
  Lit l -> return $ LitP (PatternInfo PatODot []) l
  v     -> return $ dotP v
unDotP p = return p

{-# SPECIALIZE isLitP :: Pattern' a -> TCM (Maybe Literal) #-}
isLitP :: PureTCM m => Pattern' a -> m (Maybe Literal)
isLitP (LitP _ l) = return $ Just l
isLitP (DotP _ u) = reduce u >>= \case
  Lit l -> return $ Just l
  _ -> return $ Nothing
isLitP (ConP c ci []) = do
  Con zero _ [] <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinZero
  if c == zero
    then return $ Just $ LitNat 0
    else return Nothing
isLitP (ConP c ci [a]) | visible a && isRelevant a = do
  Con suc _ [] <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinSuc
  if c == suc
    then fmap inc <$> isLitP (namedArg a)
    else return Nothing
  where
    inc :: Literal -> Literal
    inc (LitNat n) = LitNat $ n + 1
    inc _ = __IMPOSSIBLE__
isLitP _ = return Nothing

{-# SPECIALIZE unLitP :: Pattern' a -> TCM (Pattern' a) #-}
unLitP :: HasBuiltins m => Pattern' a -> m (Pattern' a)
unLitP (LitP info l@(LitNat n)) | n >= 0 = do
  Con c ci es <- constructorForm' (fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinZero)
                                  (fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinSuc)
                                  (Lit l)
  let toP (Apply (Arg i (Lit l))) = Arg i (LitP info l)
      toP _ = __IMPOSSIBLE__
      cpi   = noConPatternInfo { conPInfo = info }
  return $ ConP c cpi $ map (fmap unnamed . toP) es
unLitP p = return p
