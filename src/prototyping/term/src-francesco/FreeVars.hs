module FreeVars
  ( FreeVars(..)
  , fvAll
  , freeVars
  ) where

import           Data.Monoid                      (Monoid(mappend, mempty), (<>), mconcat)
import qualified Data.Set                         as Set
import           Bound
import           Data.Maybe                       (maybeToList)
import           Data.Foldable                    (foldMap)

import qualified Types.Signature                  as Sig
import           Types.Term
import           Types.Var
import           Eval

-- Free variables
------------------------------------------------------------------------

data FreeVars v = FreeVars
  { fvRigid    :: Set.Set v
  , fvFlexible :: Set.Set v
  }

fvAll :: Ord v => FreeVars v -> Set.Set v
fvAll fvs = fvRigid fvs <> fvFlexible fvs

instance Ord v => Monoid (FreeVars v) where
  mempty = FreeVars Set.empty Set.empty

  FreeVars rigid1 flex1 `mappend` FreeVars rigid2 flex2 =
    FreeVars (rigid1 `mappend` flex1) (rigid2 `mappend` flex2)

freeVars
  :: forall t v0. (IsVar v0, IsTerm t)
  => Sig.Signature t -> t v0 -> FreeVars v0
freeVars sig = go Just
  where
    lift :: (v -> Maybe v0) -> (TermVar v -> Maybe v0)
    lift _ (B _) = Nothing
    lift f (F v) = f v

    go :: (IsVar v) => (v -> Maybe v0) -> t v -> FreeVars v0
    go strengthen t0 = case whnfView sig t0 of
      Lam body ->
        go (lift strengthen) (fromAbs body)
      Pi domain codomain ->
        go strengthen domain <> go (lift strengthen) (fromAbs codomain)
      Equal type_ x y ->
        go strengthen type_ <> go strengthen x <> go strengthen y
      App (Var v) elims ->
        FreeVars (maybe Set.empty Set.singleton (strengthen v)) Set.empty <>
        foldMap (go strengthen) [t | Apply t <- elims]
      App (Meta mv) elims ->
        let fvs = foldMap (go strengthen) [t | Apply t <- elims]
        in FreeVars{fvRigid = Set.empty, fvFlexible = fvAll fvs}
      App (Def _) elims ->
        foldMap (go strengthen) [t | Apply t <- elims]
      App J elims ->
        foldMap (go strengthen) [t | Apply t <- elims]
      Set ->
        mempty
      Refl ->
        mempty
      Con _ args ->
        foldMap (go strengthen) args
