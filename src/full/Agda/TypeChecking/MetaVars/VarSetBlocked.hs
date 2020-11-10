module Agda.TypeChecking.MetaVars.VarSetBlocked
  (freeVarsBlocked,
   VarSetBlocked,
   freeVarsInterpolant,
   IntMap.null,
   IntMap.member,
   IntMap.lookup,
   IntMap.delete,
   IntMap.map,
   blockedOnBoth,
   subtract
  )
where

import Prelude hiding (subtract)
import qualified Prelude

import Agda.TypeChecking.Free
import qualified Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Lazy (MetaSet(..), VarMap, theVarMap)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty

import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Utils.Functor

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Blockers

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet


type VarSetBlocked = IntMap Blocker

metaSetToSet :: MetaSet -> Set MetaId
metaSetToSet = Set.fromAscList . fmap MetaId . IntSet.toAscList . theMetaSet

freeVarsBlocked :: forall v. Free v => v -> VarSetBlocked
freeVarsBlocked = fmap varOccToBlocker . theVarMap . (freeVars :: v -> VarMap)
  where
    varOccToBlocker :: VarOcc -> Blocker
    varOccToBlocker = varFlexRig <&> \case
      Flexible mvs   -> unblockOnAnyMeta (metaSetToSet mvs)
      WeaklyRigid    -> neverUnblock
      Unguarded      -> neverUnblock
      StronglyRigid  -> neverUnblock

class FreeVarsInterpolant a where
  freeVarsInterpolant :: a -> VarSetBlocked

instance FreeVarsInterpolant TwinT where
  freeVarsInterpolant :: TwinT -> VarSetBlocked
  freeVarsInterpolant (SingleT a) = freeVarsBlocked a
  freeVarsInterpolant (TwinT{twinLHS,twinRHS}) =
    IntMap.intersectionWith unblockOnEither (freeVarsBlocked twinLHS) (freeVarsBlocked twinRHS)

instance FreeVarsInterpolant a => FreeVarsInterpolant (CompareAs' a) where
  freeVarsInterpolant :: CompareAs' a -> VarSetBlocked
  freeVarsInterpolant AsSizes = IntMap.empty
  freeVarsInterpolant AsTypes = IntMap.empty
  freeVarsInterpolant (AsTermsOf a) = freeVarsInterpolant a

blockedOnBoth :: VarSetBlocked -> VarSetBlocked -> VarSetBlocked
blockedOnBoth = IntMap.unionWith unblockOnBoth

blockedOnEither :: VarSetBlocked -> VarSetBlocked -> VarSetBlocked
blockedOnEither = IntMap.unionWith unblockOnEither

subtract :: Int -> VarSetBlocked -> VarSetBlocked
subtract = IntMap.mapKeysMonotonic . flip Prelude.subtract

instance PrettyTCM VarSetBlocked where
  prettyTCM = prettyTCM . map (\(v,bs) -> (Var v [],bs)) . IntMap.toList

