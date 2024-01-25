{- | Common utilities on syntax of sized types that are shared among various components -}
module Agda.Termination.TypeBased.Common
  ( applyDataType
  , getDatatypeParametersByConstructor
  , tryReduceCopy
  , lowerIndices
  , update
  , sizeInstantiate
  ) where

import Agda.Termination.TypeBased.Syntax
import Agda.Utils.Impossible ( __IMPOSSIBLE__ )
import Agda.Syntax.Abstract.Name
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Signature
import Agda.Syntax.Internal
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Pretty
import Agda.Utils.Impossible

-- | 'applyDataType params tele' reduces arrow/parameterized 'tele' by applying 'params'
applyDataType :: [SizeType] -> SizeType  -> SizeType
applyDataType [] stele = stele
applyDataType (ct : cts) (SizeGeneric mainArgs r) = applyDataType cts (sizeInstantiate ct r)
applyDataType l@(ct : cts) (SizeGenericVar args i) = SizeGenericVar (args + length l) i
applyDataType (ct : cts) (SizeArrow (SizeTree SUndefined []) r) = applyDataType cts r
applyDataType _ (SizeTree _ _) = UndefinedSizeType -- fallback, sorry
applyDataType (UndefinedSizeType : cts) (SizeArrow _ r) = applyDataType cts r
applyDataType ts ar = __IMPOSSIBLE__

-- | 'sizeInstantiate target tele' replaces generic variables of index 0 in @tele@ with @target@
sizeInstantiate :: SizeType -> SizeType -> SizeType
sizeInstantiate = sizeInstantiate' 0

sizeInstantiate' :: Int -> SizeType -> SizeType -> SizeType
sizeInstantiate' targetIndex target (SizeArrow l r) = SizeArrow (sizeInstantiate' targetIndex target l) (sizeInstantiate' targetIndex target r)
sizeInstantiate' targetIndex target (SizeTree sd tree) = SizeTree sd (map (sizeInstantiate' targetIndex target) tree)
sizeInstantiate' targetIndex target (SizeGenericVar args i)
  | i == targetIndex = applyDataType (replicate args UndefinedSizeType) target
  | i < targetIndex  = SizeGenericVar args i
  | i > targetIndex  = SizeGenericVar args (i - 1)
sizeInstantiate' _ _ (SizeGenericVar _ _) = __UNREACHABLE__ -- stupid haskell coverage checker cannot solve the halting problem
sizeInstantiate' targetIndex target (SizeGeneric args r) = SizeGeneric args (sizeInstantiate' (targetIndex + 1) (incrementFreeGenerics 0 target) r)

incrementFreeGenerics :: Int -> SizeType -> SizeType
incrementFreeGenerics threshold (SizeArrow l r) = SizeArrow (incrementFreeGenerics threshold l) (incrementFreeGenerics threshold r)
incrementFreeGenerics threshold (SizeTree sd tree) = SizeTree sd (map (incrementFreeGenerics threshold) tree)
incrementFreeGenerics threshold (SizeGenericVar args i) = SizeGenericVar args (if i >= threshold then i + 1 else i)
incrementFreeGenerics threshold (SizeGeneric args r) = SizeGeneric args (incrementFreeGenerics (threshold + 1) r)

-- | 'instantiateGeneric f ct' replaces generic index @i@ in @tele@ with @f i@
instantiateGeneric :: Int -> (Int -> Int -> SizeType) -> SizeType -> SizeType
instantiateGeneric thr f (SizeArrow l r)  = SizeArrow (instantiateGeneric thr f l) (instantiateGeneric thr f r)
instantiateGeneric thr f (SizeGeneric args r) = SizeGeneric args (instantiateGeneric (thr + 1) (\a i -> incrementFreeGenerics 0 (f a i)) r)
instantiateGeneric thr f (SizeTree size tree) = SizeTree size (map (instantiateGeneric thr f) tree)
instantiateGeneric thr f (SizeGenericVar args i) = if i < thr then SizeGenericVar args i else f args (i - thr)

getDatatypeParametersByConstructor :: QName -> TCM Int
getDatatypeParametersByConstructor conName = do
  def <- theDef <$> getConstInfo conName
  case def of
    Constructor { conData } -> do
      dataInfo <- theDef <$> getConstInfo conData
      case dataInfo of
        Datatype { dataPars } -> pure dataPars
        Record { recPars } -> pure recPars
        _ -> __IMPOSSIBLE__
    _ -> __IMPOSSIBLE__

-- | The definitions that are obtained by instantiation of a module has a type signature affected by that module.
--   In particular, it means that eliminations in the application do not match the type of the eliminated term.
--   This poses problems for type-based termination, since it also emulates β-reduction.
tryReduceCopy :: Term -> TCM Term
tryReduceCopy t@(Def qn elims) = do
  reduced <- reduceDefCopyTCM qn elims
  case reduced of
    NoReduction _ -> pure t
    YesReduction _ t -> do
      reportSDoc "term.tbt" 20 $ "Successfully reduced definition" <+> prettyTCM qn
      tryReduceCopy t
tryReduceCopy (Con ch ci elims) = do
  reduced <- reduceDefCopyTCM (conName ch) elims
  case reduced of
    NoReduction _ -> pure $ Con ch ci elims
    YesReduction _ t -> do
      reportSDoc "term.tbt" 20 $ "Successfully reduced definition" <+> prettyTCM (conName ch)
      tryReduceCopy t
tryReduceCopy t = pure t

lowerIndices :: SizeSignature -> SizeSignature
lowerIndices (SizeSignature bounds contra tele) =
  let minIndex = minimalIndex tele
  in SizeSignature
      (map (\case
         SizeBounded i -> SizeBounded (i - minIndex)
         SizeUnbounded -> SizeUnbounded) bounds)
      (map (\x -> x - minIndex) contra)
      (update (\x -> x - minIndex) tele)


update :: (Int -> Int) -> SizeType -> SizeType
update subst (SizeTree size tree) = SizeTree (weakenSize size) (map (update subst) tree)
  where
    weakenSize :: Size -> Size
    weakenSize SUndefined = SUndefined
    weakenSize (SDefined i) = SDefined (subst i)
update subst (SizeArrow l r) = SizeArrow (update subst l) (update subst r)
update subst (SizeGeneric args r) = SizeGeneric args (update subst r)
update subst (SizeGenericVar args i) = SizeGenericVar args i

minimalIndex :: SizeType -> Int
minimalIndex (SizeArrow l r) = min (minimalIndex l) (minimalIndex r)
minimalIndex (SizeGeneric _ r) = minimalIndex r
minimalIndex (SizeGenericVar _ _) = maxBound
minimalIndex (SizeTree s rest) = minimum ((extractFromSize s) : map minimalIndex rest)
  where
    extractFromSize :: Size -> Int
    extractFromSize (SDefined i) = i
    extractFromSize (SUndefined) = maxBound
