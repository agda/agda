{- | Common utilities on syntax of sized types that are shared among various components -}
module Agda.Termination.TypeBased.Common
  ( applyDataType
  , getDatatypeParametersByConstructor
  , tryReduceCopy
  , lowerIndices
  , update
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

-- | 'applyDataType params tele' reduces arrow/parameterized 'tele' by applying 'params'. This is the way to instantiate generics.
applyDataType :: [SizeTele] -> SizeTele -> SizeTele
applyDataType params tele = applyDataType' params tele (\args i -> SizeGenericVar args i)

applyDataType' :: [SizeTele] -> SizeTele -> (Int -> Int -> SizeTele) -> SizeTele
applyDataType' [] stele f = instantiateGeneric f stele
applyDataType' (ct : cts) (SizeGeneric mainArgs i r) f = applyDataType' cts r (\args j -> if i == j then (applyDataType (replicate args UndefinedSizeTele) ct) else f args j)
applyDataType' l@(ct : cts) (SizeGenericVar args i) f = SizeGenericVar (args + length l) i
applyDataType' (ct : cts) (SizeArrow (SizeTree SUndefined []) r) f = applyDataType' cts r f
applyDataType' _ (SizeTree _ _) f = UndefinedSizeTele -- fallback, sorry
applyDataType' (UndefinedSizeTele : cts) (SizeArrow _ r) f = applyDataType' cts r f
applyDataType' ts ar f = __IMPOSSIBLE__

-- | 'instantiateGeneric f ct' replaces generic index @i@ in @tele@ with @f i@
instantiateGeneric :: (Int -> Int -> SizeTele) -> SizeTele -> SizeTele
instantiateGeneric f (SizeArrow l r)  = SizeArrow (instantiateGeneric f l) (instantiateGeneric f r)
instantiateGeneric f (SizeGeneric args x r) = SizeGeneric args x (instantiateGeneric f r)
instantiateGeneric f (SizeTree size tree) = SizeTree size (map (instantiateGeneric f) tree)
instantiateGeneric f (SizeGenericVar args i) = f args i

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


update :: (Int -> Int) -> SizeTele -> SizeTele
update subst (SizeTree size tree) = SizeTree (weakenSize size) (map (update subst) tree)
  where
    weakenSize :: Size -> Size
    weakenSize SUndefined = SUndefined
    weakenSize (SDefined i) = SDefined (subst i)
update subst (SizeArrow l r) = SizeArrow (update subst l) (update subst r)
update subst(SizeGeneric args i r) = SizeGeneric args i (update subst r)
update subst (SizeGenericVar args i) = SizeGenericVar args i

minimalIndex :: SizeTele -> Int
minimalIndex (SizeArrow l r) = min (minimalIndex l) (minimalIndex r)
minimalIndex (SizeGeneric _ _ r) = minimalIndex r
minimalIndex (SizeGenericVar _ _) = maxBound
minimalIndex (SizeTree s rest) = minimum ((extractFromSize s) : map minimalIndex rest)
  where
    extractFromSize :: Size -> Int
    extractFromSize (SDefined i) = i
    extractFromSize (SUndefined) = maxBound
