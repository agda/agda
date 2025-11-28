{-# OPTIONS -Wunused-imports #-}

module Agda.TypeChecking.Coverage.SplitPattern
  ( SplitPattern, SplitPatVar(..)
  , fromSplitPattern, fromSplitPatterns, toSplitPatterns
  , toSplitPSubst, applySplitPSubst
  , isTrivialPattern
  ) where

import Prelude hiding ( null )

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty ( PrettyTCM(..) )
import Agda.TypeChecking.Records
import Agda.TypeChecking.Substitute

import Agda.Utils.Null
import Agda.Syntax.Common.Pretty ( Pretty(..), text, prettyList_ )
import Agda.Utils.Monad

import Agda.Utils.Impossible
import Agda.Syntax.Position (KillRange, killRange, killRangeN)

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

instance KillRange SplitPatVar where
  killRange (SplitPatVar n i lits) = killRangeN SplitPatVar n i lits

type SplitPattern = Pattern' SplitPatVar

toSplitVar :: DBPatVar -> SplitPatVar
toSplitVar x = SplitPatVar (dbPatVarName x) (dbPatVarIndex x) []

fromSplitVar :: SplitPatVar -> DBPatVar
fromSplitVar x = DBPatVar (splitPatVarName x) (splitPatVarIndex x)

instance DeBruijn SplitPatVar where
  deBruijnView x = deBruijnView (fromSplitVar x)
  deBruijnNamedVar n i = toSplitVar (deBruijnNamedVar n i)

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

  applySubst' = applySubst -- TODO
