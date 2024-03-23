{- | Common utilities on syntax of sized types that are shared among various components -}
module Agda.Termination.TypeBased.Common
  ( applyDataType
  , getDatatypeParametersByConstructor
  , tryReduceCopy
  , updateSizeVariables
  , sizeInstantiate
  , SizeDecomposition(..)
  , computeDecomposition
  , fixGaps
  ) where


import Control.Arrow (second)
import Data.IntSet (IntSet)
import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import Data.Maybe (mapMaybe)

import Agda.Syntax.Abstract.Name ( QName )
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal ( QName, Term(Con, Def), ConHead(conName) )
import Agda.Termination.TypeBased.Syntax ( SizeSignature(SizeSignature), SizeBound(SizeUnbounded, SizeBounded), SizeType(..),  Size(..), pattern UndefinedSizeType )
import Agda.TypeChecking.Monad.Base ( TCM, Definition(theDef), Reduced(YesReduction, NoReduction), pattern Constructor, conData, pattern Record, recPars, pattern Datatype, dataPars )
import Agda.TypeChecking.Monad.Debug ( reportSDoc )
import Agda.TypeChecking.Monad.Signature ( HasConstInfo(getConstInfo) )
import Agda.TypeChecking.Polarity.Base (Polarity(..))
import Agda.TypeChecking.Polarity ( composePol, neg )
import Agda.TypeChecking.Pretty ( PrettyTCM(prettyTCM), (<+>) )
import Agda.TypeChecking.Reduce ( reduceDefCopyTCM )
import Agda.Utils.Impossible ( __IMPOSSIBLE__, __UNREACHABLE__ )

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

-- | 'sizeInstantiate' that is adapted to De Bruijn indices
sizeInstantiate' :: Int -> SizeType -> SizeType -> SizeType
sizeInstantiate' targetIndex target (SizeArrow l r) = SizeArrow (sizeInstantiate' targetIndex target l) (sizeInstantiate' targetIndex target r)
sizeInstantiate' targetIndex target (SizeTree sd tree) = SizeTree sd (map (second $ sizeInstantiate' targetIndex target) tree)
sizeInstantiate' targetIndex target (SizeGenericVar args i)
  | i < targetIndex  = SizeGenericVar args i
  | i > targetIndex  = SizeGenericVar args (i - 1)
  | otherwise        = applyDataType (replicate args UndefinedSizeType) target
sizeInstantiate' targetIndex target (SizeGeneric args r) = SizeGeneric args (sizeInstantiate' (targetIndex + 1) (incrementFreeGenerics 0 target) r)

-- | Increments all De Bruijn indices for second-order variables. This is needed to correctly handle "free" generic variables.
incrementFreeGenerics :: Int -> SizeType -> SizeType
incrementFreeGenerics threshold (SizeArrow l r) = SizeArrow (incrementFreeGenerics threshold l) (incrementFreeGenerics threshold r)
incrementFreeGenerics threshold (SizeTree sd tree) = SizeTree sd (map (second $ incrementFreeGenerics threshold) tree)
incrementFreeGenerics threshold (SizeGenericVar args i) = SizeGenericVar args (if i >= threshold then i + 1 else i)
incrementFreeGenerics threshold (SizeGeneric args r) = SizeGeneric args (incrementFreeGenerics (threshold + 1) r)

-- | Extracts the number of parameters for a constructor.
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
      reportSDoc "term.tbt" 80 $ "Successfully reduced a copied definition" <+> prettyTCM qn
      tryReduceCopy t
tryReduceCopy (Con ch ci elims) = do
  reduced <- reduceDefCopyTCM (conName ch) elims
  case reduced of
    NoReduction _ -> pure $ Con ch ci elims
    YesReduction _ t -> do
      reportSDoc "term.tbt" 80 $ "Successfully reduced a copied constructor" <+> prettyTCM (conName ch)
      tryReduceCopy t
tryReduceCopy t = pure t

-- | Represents decomposition of a set of size variables for some size signature based on polarities
data SizeDecomposition = SizeDecomposition
  { sdPositive :: [Int] -- ^ Size variables occurring positively
  , sdNegative :: [Int] -- ^ Size variables occurring negatively
  , sdOther    :: [Int] -- ^ Remaining size variables, that have mixed and unused variance.
  } deriving Show


-- The decomposition should proceed alongside polarity, i.e. doubly negative occurences of inductive types are also subject of size preservation.
computeDecomposition :: IntSet -> SizeType -> SizeDecomposition
computeDecomposition coinductiveVars sizeType =
  let (positiveVariables, negativeVariables, rest) = collectPolarizedSizes Covariant sizeType
      (coinductivePositive, inductivePositive) = List.partition (`IntSet.member` coinductiveVars) positiveVariables
      (coinductiveNegative, inductiveNegative) = List.partition (`IntSet.member` coinductiveVars) negativeVariables
  in SizeDecomposition
    { sdPositive = coinductiveNegative ++ inductivePositive
    , sdNegative = inductiveNegative ++ coinductivePositive
    , sdOther = rest }
 where
    collectPolarizedSizes :: Polarity -> SizeType -> ([Int], [Int], [Int])
    collectPolarizedSizes pol (SizeTree size ts) =
      let selector = case size of
            SUndefined -> id
            SDefined i -> case pol of
              Covariant -> (\(a, b, c) -> (i : a, b, c))
              Contravariant -> (\(a, b, c) -> (a, (i : b), c))
              _ -> (\(a, b, c) -> (a, b, i : c))
          ind = map (\(p, t) -> collectPolarizedSizes (composePol p pol) t) ts
      in selector (concatMap (\(a, _, _) -> a) ind, concatMap (\(_, b, _) -> b) ind, concatMap (\(_, _, c) -> c) ind)
    collectPolarizedSizes pol (SizeArrow l r) =
      let (f1, f2, f3) = collectPolarizedSizes (neg pol) l
          (s1, s2, s3) = collectPolarizedSizes pol r
      in (f1 ++ s1, f2 ++ s2, f3 ++ s3)
    collectPolarizedSizes pol (SizeGeneric _ r) = collectPolarizedSizes pol r
    collectPolarizedSizes _ (SizeGenericVar _ i) = ([], [], [])

-- | Reassignes all size variable in a signature, such that the resulting signature uses a continuous region of indices starting from 0.
-- This function is needed because encoding may procedures do not guarantee that the sizes in the encoded signature are continuous.
-- The reason for this is System Fω, which does not allow to express a dependently-typed signature completely.
fixGaps :: SizeSignature -> SizeSignature
fixGaps (SizeSignature bounds contra tele) =
  let decomp = computeDecomposition (IntSet.fromList contra) tele
      subst = IntMap.fromList $ (zip (sdNegative decomp ++ sdOther decomp ++ sdPositive decomp) [0..])
  in SizeSignature (rearrangeBounds bounds subst) (mapMaybe (subst IntMap.!?) contra) (updateSizeVariables (subst IntMap.!) tele)
  where
    mapBound :: SizeBound -> IntMap Int -> SizeBound
    mapBound SizeUnbounded _ = SizeUnbounded
    mapBound (SizeBounded i) subst = SizeBounded (subst IntMap.! i)

    rearrangeBounds :: [SizeBound] -> IntMap Int -> [SizeBound]
    rearrangeBounds bounds subst = map snd $ List.sortOn fst (mapMaybe (\(i, b) -> (, mapBound b subst) <$> (subst IntMap.!? i) ) (zip [0..] bounds))

-- | Applies a function to all size variables in a signature.
updateSizeVariables :: (Int -> Int) -> SizeType -> SizeType
updateSizeVariables subst (SizeTree size tree) = SizeTree (weakenSize size) (map (second $ updateSizeVariables subst) tree)
  where
    weakenSize :: Size -> Size
    weakenSize SUndefined = SUndefined
    weakenSize (SDefined i) = SDefined (subst i)
updateSizeVariables subst (SizeArrow l r) = SizeArrow (updateSizeVariables subst l) (updateSizeVariables subst r)
updateSizeVariables subst (SizeGeneric args r) = SizeGeneric args (updateSizeVariables subst r)
updateSizeVariables subst (SizeGenericVar args i) = SizeGenericVar args i
