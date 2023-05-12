{-# LANGUAGE NondecreasingIndentation #-}

module Agda.TypeChecking.Rules.Builtin
  ( bindBuiltin
  , bindBuiltinNoDef
  , builtinKindOfName
  , bindPostulatedName
  , isUntypedBuiltin
  , bindUntypedBuiltin
  ) where

import Prelude hiding (null)

import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans.Maybe

import Data.List (find, sortBy)
import Data.Function (on)

import Agda.Interaction.Options.Base

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.TypeChecking.Monad

import qualified Agda.TypeChecking.CompiledClause as CC
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Constraints ( noConstraints )
import Agda.TypeChecking.EtaContract
import Agda.TypeChecking.Functions
import Agda.TypeChecking.Names
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Rules.Term ( checkExpr , inferExpr )
import Agda.TypeChecking.Warnings

import {-# SOURCE #-} Agda.TypeChecking.Rules.Builtin.Coinduction
import {-# SOURCE #-} Agda.TypeChecking.Rewriting

import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.List1 (pattern (:|))
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Size

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Checking builtin pragmas
---------------------------------------------------------------------------

builtinPostulate :: TCM Type -> BuiltinDescriptor
builtinPostulate = BuiltinPostulate Relevant

builtinPostulateC :: Cubical -> TCM Type -> BuiltinDescriptor
builtinPostulateC c m =
  BuiltinPostulate Relevant $ requireCubical c "" >> m

findBuiltinInfo :: BuiltinId -> Maybe BuiltinInfo
findBuiltinInfo b = find ((b ==) . builtinName) coreBuiltins

coreBuiltins :: [BuiltinInfo]
coreBuiltins =
  [ (builtinList                             |-> BuiltinData (tset --> tset) [builtinNil, builtinCons])
  , (builtinArg                              |-> BuiltinData (tset --> tset) [builtinArgArg])
  , (builtinAbs                              |-> BuiltinData (tset --> tset) [builtinAbsAbs])
  , (builtinArgInfo                          |-> BuiltinData tset [builtinArgArgInfo])
  , (builtinBool                             |-> BuiltinData tset [builtinTrue, builtinFalse])
  , (builtinNat                              |-> BuiltinData tset [builtinZero, builtinSuc])
  , (builtinMaybe                            |-> BuiltinData (tset --> tset) [builtinNothing, builtinJust])
  , (builtinSigma                            |-> BuiltinData (runNamesT [] $
                                                              hPi' "la" (el $ cl primLevel) $ \ a ->
                                                              hPi' "lb" (el $ cl primLevel) $ \ b ->
                                                              nPi' "A" (sort . tmSort <$> a) $ \bA ->
                                                              nPi' "B" (el' a bA --> (sort . tmSort <$> b)) $ \bB ->
                                                              ((sort . tmSort) <$> (cl primLevelMax <@> a <@> b))
                                                              )
                                                             [BuiltinSigmaCon])
  , (builtinUnit                             |-> BuiltinData tset [builtinUnitUnit])  -- actually record, but they are treated the same
  , (builtinAgdaLiteral                      |-> BuiltinData tset [builtinAgdaLitNat, builtinAgdaLitWord64, builtinAgdaLitFloat,
                                                                   builtinAgdaLitChar, builtinAgdaLitString,
                                                                   builtinAgdaLitQName, builtinAgdaLitMeta])
  , (builtinAgdaPattern                      |-> BuiltinData tset [builtinAgdaPatVar, builtinAgdaPatCon, builtinAgdaPatDot,
                                                                   builtinAgdaPatLit, builtinAgdaPatProj, builtinAgdaPatAbsurd])
  , (builtinAgdaPatVar                       |-> BuiltinDataCons (tnat --> tpat))
  , (builtinAgdaPatCon                       |-> BuiltinDataCons (tqname --> tlist (targ tpat) --> tpat))
  , (builtinAgdaPatDot                       |-> BuiltinDataCons (tterm --> tpat))
  , (builtinAgdaPatLit                       |-> BuiltinDataCons (tliteral --> tpat))
  , (builtinAgdaPatProj                      |-> BuiltinDataCons (tqname --> tpat))
  , (builtinAgdaPatAbsurd                    |-> BuiltinDataCons (tnat --> tpat))
  , (builtinLevel                            |-> builtinPostulate tLevelUniv)
  , (builtinWord64                           |-> builtinPostulate tset)
  , (builtinInteger                          |-> BuiltinData tset [builtinIntegerPos, builtinIntegerNegSuc])
  , (builtinIntegerPos                       |-> BuiltinDataCons (tnat --> tinteger))
  , (builtinIntegerNegSuc                    |-> BuiltinDataCons (tnat --> tinteger))
  , (builtinFloat                            |-> builtinPostulate tset)
  , (builtinChar                             |-> builtinPostulate tset)
  , (builtinString                           |-> builtinPostulate tset)
  , (builtinQName                            |-> builtinPostulate tset)
  , (builtinAgdaMeta                         |-> builtinPostulate tset)
  , (builtinIO                               |-> builtinPostulate (tset --> tset))
  , (builtinPath                             |-> BuiltinUnknown
                                                             (Just $ requireCubical CErased "" >>
                                                             hPi "a" (el primLevel) (
                                                              hPi "A" (return $ sort $ varSort 0) $
                                                              (El (varSort 1) <$> varM 0) -->
                                                              (El (varSort 1) <$> varM 0) -->
                                                              return (sort $ varSort 1)))
                                                             verifyPath)
  , (builtinPathP                            |-> builtinPostulateC CErased (hPi "a" (el primLevel) $
                                                              nPi "A" (tinterval --> return (sort $ varSort 0)) $
                                                              (El (varSort 1) <$> varM 0 <@> primIZero) -->
                                                              (El (varSort 1) <$> varM 0 <@> primIOne) -->
                                                              return (sort $ varSort 1)))
  , (builtinIntervalUniv                     |-> BuiltinSort SortIntervalUniv)
  , (builtinInterval                         |-> BuiltinData (requireCubical CErased "" >>
                                                              (return $ sort IntervalUniv)) [builtinIZero,builtinIOne])
  , (builtinSub                              |-> builtinPostulateC CErased (runNamesT [] $ hPi' "a" (el $ cl primLevel) $ \ a ->
                                                                   nPi' "A" (el' (cl primLevelSuc <@> a) (Sort . tmSort <$> a)) $ \ bA ->
                                                                   nPi' "φ" (cl tinterval) $ \ phi ->
                                                                   el's a (cl primPartial <#> a <@> phi <@> bA) --> (ssort . atomicLevel <$> a)
                                                                  ))
  , (builtinSubIn                            |-> builtinPostulateC CErased (runNamesT [] $
                                                                   hPi' "a" (el $ cl primLevel) $ \ a ->
                                                                   hPi' "A" (el' (cl primLevelSuc <@> a) (Sort . tmSort <$> a)) $ \ bA ->
                                                                   hPi' "φ" (cl tinterval) $ \ phi ->
                                                                   nPi' "x" (el' a bA) $ \ x ->
                                                                   el's a $ cl primSub <#> a <@> bA <@> phi <@> lam "o" (\ _ -> x)))
  , (builtinIZero                            |-> BuiltinDataCons tinterval)
  , (builtinIOne                             |-> BuiltinDataCons tinterval)
  , (builtinPartial                          |-> BuiltinPrim PrimPartial (const $ return ()))
  , (builtinPartialP                         |-> BuiltinPrim PrimPartialP (const $ return ()))
  , (builtinIsOne                            |-> builtinPostulateC CErased (tinterval --> return (ssort $ ClosedLevel 0)))
  , (builtinItIsOne                          |-> builtinPostulateC CErased (elSSet $ primIsOne <@> primIOne))
  , (builtinIsOne1                           |-> builtinPostulateC CErased (runNamesT [] $
                                                                   nPi' "i" (cl tinterval) $ \ i ->
                                                                   nPi' "j" (cl tinterval) $ \ j ->
                                                                   nPi' "i1" (elSSet $ cl primIsOne <@> i) $ \ i1 ->
                                                                   (elSSet $ cl primIsOne <@> (cl primIMax <@> i <@> j))))
  , (builtinIsOne2                           |-> builtinPostulateC CErased (runNamesT [] $
                                                                   nPi' "i" (cl tinterval) $ \ i ->
                                                                   nPi' "j" (cl tinterval) $ \ j ->
                                                                   nPi' "j1" (elSSet $ cl primIsOne <@> j) $ \ j1 ->
                                                                   (elSSet $ cl primIsOne <@> (cl primIMax <@> i <@> j))))
  , (builtinIsOneEmpty                       |-> builtinPostulateC CErased (runNamesT [] $
                                                                   hPi' "l" (el $ cl primLevel) $ \ l ->
                                                                   hPi' "A" (pPi' "o" (cl primIZero) $ \ _ ->
                                                                                  el' (cl primLevelSuc <@> l) (Sort . tmSort <$> l)) $ \ bA ->
                                                                   pPi' "o" (cl primIZero) (\ o ->
                                                                        el' l $ gApply' (setRelevance Irrelevant defaultArgInfo) bA o)))

  , (builtinId                               |-> BuiltinData ((>>) (requireCubical CErased "") $ hPi "a" (el primLevel) $
                                                              hPi "A" (return $ sort $ varSort 0) $
                                                              (El (varSort 1) <$> varM 0) -->
                                                              (El (varSort 1) <$> varM 0) -->
                                                             return (sort $ varSort 1)) [builtinReflId])
  , (builtinReflId                           |-> BuiltinDataCons ((>>) (requireCubical CErased "") $ runNamesT [] $
                                                              hPi' "a" (el primLevel) $ \ l ->
                                                              hPi' "A" (sort . tmSort <$> l) $ \ bA ->
                                                              hPi' "x" (el' l bA) $ \ x ->
                                                              el' l (primId <#> l <#> bA <@> x <@> x)))
  , (builtinEquiv                            |-> BuiltinUnknown (Just $ requireCubical CErased "" >> runNamesT [] (
                                                                    hPi' "l" (el $ cl primLevel) $ \ a ->
                                                                    hPi' "l'" (el $ cl primLevel) $ \ b ->
                                                                    nPi' "A" (sort . tmSort <$> a) $ \bA ->
                                                                    nPi' "B" (sort . tmSort <$> b) $ \bB ->
                                                                    ((sort . tmSort) <$> (cl primLevelMax <@> a <@> b))
                                                                  ))
                                                                   (const $ const $ return ()))
  , (builtinEquivFun                         |-> BuiltinUnknown (Just $ requireCubical CErased "" >> runNamesT [] (
                                                                 hPi' "l" (el $ cl primLevel) $ \ a ->
                                                                 hPi' "l'" (el $ cl primLevel) $ \ b ->
                                                                 hPi' "A" (sort . tmSort <$> a) $ \bA ->
                                                                 hPi' "B" (sort . tmSort <$> b) $ \bB ->
                                                                 el' (cl primLevelMax <@> a <@> b) (cl primEquiv <#> a <#> b <@> bA <@> bB) -->
                                                                 (el' a bA --> el' b bB)
                                                               ))
                                                                (const $ const $ return ()))
  , (builtinEquivProof                       |-> BuiltinUnknown (Just $ requireCubical CErased "" >> runNamesT [] (
                                                               hPi' "l" (el $ cl primLevel) $ \ la ->
                                                               hPi' "l'" (el $ cl primLevel) $ \ lb ->
                                                               nPi' "A" (sort . tmSort <$> la) $ \ bA ->
                                                               nPi' "B" (sort . tmSort <$> lb) $ \ bB ->
                                                               nPi' "e" (el' (cl primLevelMax <@> la <@> lb)
                                                                             (cl primEquiv <#> la <#> lb <@> bA <@> bB)) $ \ e -> do
                                                               nPi' "b" (el' lb bB) $ \ b -> do
                                                                let f = cl primEquivFun <#> la <#> lb <#> bA <#> bB <@> e
                                                                    lub = cl primLevelMax <@> la <@> lb
                                                                    fiber = el' lub
                                                                                (cl primSigma <#> la <#> lb
                                                                                  <@> bA
                                                                                  <@> lam "a" (\ a ->
                                                                                         cl primPath <#> lb <#> bB <@> (f <@> a) <@> b))
                                                                nPi' "φ" (cl tinterval) $ \ phi ->
                                                                  nPi' "f" (pPi' "o" phi (\ o -> fiber)) $ \ pfib ->
                                                                    el' lub (cl primSub <#> lub <#> fmap unEl fiber <@> phi <@> pfib)
                                                             ))
                                                              (const $ const $ return ()))
  , (builtinTranspProof                       |-> BuiltinUnknown (Just $ requireCubical CErased "" >> runNamesT [] (
                                                               hPi' "l" (el $ cl primLevel) $ \ la -> do
                                                               nPi' "e" (cl tinterval --> (sort . tmSort <$> la)) $ \ e -> do
                                                               let lb = la; bA = e <@> cl primIZero; bB = e <@> cl primIOne
                                                               nPi' "φ" (cl tinterval) $ \ phi -> do
                                                               nPi' "a" (pPi' "o" phi (\ _ -> el' la bA)) $ \ a -> do
                                                               let f = cl primTrans <#> lam "i" (\ _ -> la) <@> e <@> cl primIZero
                                                                   z = ilam "o" $ \ o -> f <@> (a <@> o)
                                                               nPi' "b" (el's lb (cl primSub <#> lb <@> bB <@> phi <@> z)) $ \ b' -> do
                                                               let b = cl primSubOut <#> lb <#> bB <#> phi <#> z <@> b'
                                                                   fiber = el' la
                                                                               (cl primSigma <#> la <#> lb
                                                                                  <@> bA
                                                                                  <@> lam "a" (\ a ->
                                                                                         cl primPath <#> lb <#> bB <@> (f <@> a) <@> b))
                                                               fiber
                                                             ))
                                                              (const $ const $ return ()))
  , (builtinAgdaSort                         |-> BuiltinData tset
                                                   [ builtinAgdaSortSet, builtinAgdaSortLit
                                                   , builtinAgdaSortProp, builtinAgdaSortPropLit
                                                   , builtinAgdaSortInf, builtinAgdaSortUnsupported])
  , (builtinAgdaTerm                         |-> BuiltinData tset
                                                   [ builtinAgdaTermVar, builtinAgdaTermLam, builtinAgdaTermExtLam
                                                   , builtinAgdaTermDef, builtinAgdaTermCon
                                                   , builtinAgdaTermPi, builtinAgdaTermSort
                                                   , builtinAgdaTermLit, builtinAgdaTermMeta
                                                   , builtinAgdaTermUnsupported])
  , builtinAgdaErrorPart                     |-> BuiltinData tset [ builtinAgdaErrorPartString, builtinAgdaErrorPartTerm, builtinAgdaErrorPartPatt, builtinAgdaErrorPartName ]
  , builtinAgdaErrorPartString               |-> BuiltinDataCons (tstring --> terrorpart)
  , builtinAgdaErrorPartTerm                 |-> BuiltinDataCons (tterm --> terrorpart)
  , builtinAgdaErrorPartPatt                 |-> BuiltinDataCons (tpat --> terrorpart)
  , builtinAgdaErrorPartName                 |-> BuiltinDataCons (tqname --> terrorpart)
  -- Andreas, 2017-01-12, issue #2386: special handling of builtinEquality
  -- , (builtinEquality                         |-> BuiltinData (hPi "a" (el primLevel) $
  --                                                             hPi "A" (return $ sort $ varSort 0) $
  --                                                             (El (varSort 1) <$> varM 0) -->
  --                                                             (El (varSort 1) <$> varM 0) -->
  --                                                             return (sort $ varSort 1))
  --                                                            [builtinRefl])
  , (builtinHiding                           |-> BuiltinData tset [builtinHidden, builtinInstance, builtinVisible])
    -- Relevance
  , (builtinRelevance                        |-> BuiltinData tset [builtinRelevant, builtinIrrelevant])
  , (builtinRelevant                         |-> BuiltinDataCons trelevance)
  , (builtinIrrelevant                       |-> BuiltinDataCons trelevance)
    -- Quantity
  , (builtinQuantity                         |-> BuiltinData tset [builtinQuantity0, builtinQuantityω])
  , (builtinQuantity0                        |-> BuiltinDataCons tquantity)
  , (builtinQuantityω                        |-> BuiltinDataCons tquantity)
    -- Modality
  , (builtinModality                         |-> BuiltinData tset [builtinModalityConstructor])
  , (builtinModalityConstructor              |-> BuiltinDataCons (trelevance --> tquantity --> tmodality))
    -- Associativity
  , builtinAssoc                             |-> BuiltinData tset [builtinAssocLeft, builtinAssocRight, builtinAssocNon]
  , builtinAssocLeft                         |-> BuiltinDataCons tassoc
  , builtinAssocRight                        |-> BuiltinDataCons tassoc
  , builtinAssocNon                          |-> BuiltinDataCons tassoc
    -- Precedence
  , builtinPrecedence                        |-> BuiltinData tset [builtinPrecRelated, builtinPrecUnrelated]
  , builtinPrecRelated                       |-> BuiltinDataCons (tfloat --> tprec)
  , builtinPrecUnrelated                     |-> BuiltinDataCons tprec
    -- Fixity
  , builtinFixity                            |-> BuiltinData tset [builtinFixityFixity]
  , builtinFixityFixity                      |-> BuiltinDataCons (tassoc --> tprec --> tfixity)
  -- Andreas, 2017-01-12, issue #2386: special handling of builtinEquality
  -- , (builtinRefl                             |-> BuiltinDataCons (hPi "a" (el primLevel) $
  --                                                                 hPi "A" (return $ sort $ varSort 0) $
  --                                                                 hPi "x" (El (varSort 1) <$> varM 0) $
  --                                                                 El (varSort 2) <$> primEquality <#> varM 2 <#> varM 1 <@> varM 0 <@> varM 0))
  , (builtinRewrite                          |-> BuiltinUnknown Nothing verifyBuiltinRewrite)
  , (builtinNil                              |-> BuiltinDataCons (hPi "A" tset (el (list v0))))
  , (builtinCons                             |-> BuiltinDataCons (hPi "A" tset (tv0 --> el (list v0) --> el (list v0))))
  , (builtinNothing                          |-> BuiltinDataCons (hPi "A" tset (el (tMaybe v0))))
  , (builtinJust                             |-> BuiltinDataCons (hPi "A" tset (tv0 --> el (tMaybe v0))))
  , (builtinZero                             |-> BuiltinDataCons tnat)
  , (builtinSuc                              |-> BuiltinDataCons (tnat --> tnat))
  , (builtinTrue                             |-> BuiltinDataCons tbool)
  , (builtinFalse                            |-> BuiltinDataCons tbool)
  , (builtinArgArg                           |-> BuiltinDataCons (hPi "A" tset (targinfo --> tv0 --> targ tv0)))
  , (builtinAbsAbs                           |-> BuiltinDataCons (hPi "A" tset (tstring  --> tv0 --> tabs tv0)))
  , (builtinArgArgInfo                       |-> BuiltinDataCons (thiding --> tmodality --> targinfo))
  , (builtinAgdaTermVar                      |-> BuiltinDataCons (tnat --> targs --> tterm))
  , (builtinAgdaTermLam                      |-> BuiltinDataCons (thiding --> tabs tterm --> tterm))
  , (builtinAgdaTermExtLam                   |-> BuiltinDataCons (tlist tclause --> targs --> tterm))
  , (builtinAgdaTermDef                      |-> BuiltinDataCons (tqname --> targs --> tterm))
  , (builtinAgdaTermCon                      |-> BuiltinDataCons (tqname --> targs --> tterm))
  , (builtinAgdaTermPi                       |-> BuiltinDataCons (targ ttype --> tabs ttype --> tterm))
  , (builtinAgdaTermSort                     |-> BuiltinDataCons (tsort --> tterm))
  , (builtinAgdaTermLit                      |-> BuiltinDataCons (tliteral --> tterm))
  , (builtinAgdaTermMeta                     |-> BuiltinDataCons (tmeta --> targs --> tterm))
  , (builtinAgdaTermUnsupported              |-> BuiltinDataCons tterm)
  , (builtinAgdaLitNat                       |-> BuiltinDataCons (tnat --> tliteral))
  , (builtinAgdaLitWord64                    |-> BuiltinDataCons (tword64 --> tliteral))
  , (builtinAgdaLitFloat                     |-> BuiltinDataCons (tfloat --> tliteral))
  , (builtinAgdaLitChar                      |-> BuiltinDataCons (tchar --> tliteral))
  , (builtinAgdaLitString                    |-> BuiltinDataCons (tstring --> tliteral))
  , (builtinAgdaLitQName                     |-> BuiltinDataCons (tqname --> tliteral))
  , (builtinAgdaLitMeta                      |-> BuiltinDataCons (tmeta --> tliteral))
  , (builtinHidden                           |-> BuiltinDataCons thiding)
  , (builtinInstance                         |-> BuiltinDataCons thiding)
  , (builtinVisible                          |-> BuiltinDataCons thiding)
  , (builtinSizeUniv                         |-> builtinPostulate tsetOmega) -- SizeUniv : Setω
  , (builtinSize                             |-> builtinPostulate tSizeUniv)
  , (builtinSizeLt                           |-> builtinPostulate (tsize ..--> tSizeUniv))
  , (builtinSizeSuc                          |-> builtinPostulate (tsize --> tsize))
  , (builtinSizeInf                          |-> builtinPostulate tsize)
  -- postulate max : {i : Size} -> Size< i -> Size< i -> Size< i
  , (builtinSizeMax                          |-> builtinPostulate (tsize --> tsize --> tsize))
     -- (hPi "i" tsize $ let a = el $ primSizeLt <@> v0 in (a --> a --> a)))
  , (builtinAgdaSortSet                      |-> BuiltinDataCons (tterm --> tsort))
  , (builtinAgdaSortLit                      |-> BuiltinDataCons (tnat --> tsort))
  , (builtinAgdaSortProp                     |-> BuiltinDataCons (tterm --> tsort))
  , (builtinAgdaSortPropLit                  |-> BuiltinDataCons (tnat --> tsort))
  , (builtinAgdaSortInf                      |-> BuiltinDataCons (tnat --> tsort))
  , (builtinAgdaSortUnsupported              |-> BuiltinDataCons tsort)
  , (builtinNatPlus                          |-> BuiltinPrim PrimNatPlus verifyPlus)
  , (builtinNatMinus                         |-> BuiltinPrim PrimNatMinus verifyMinus)
  , (builtinNatTimes                         |-> BuiltinPrim PrimNatTimes verifyTimes)
  , (builtinNatDivSucAux                     |-> BuiltinPrim PrimNatDivSucAux verifyDivSucAux)
  , (builtinNatModSucAux                     |-> BuiltinPrim PrimNatModSucAux verifyModSucAux)
  , (builtinNatEquals                        |-> BuiltinPrim PrimNatEquality verifyEquals)
  , (builtinNatLess                          |-> BuiltinPrim PrimNatLess verifyLess)
  , (builtinLevelUniv                        |-> BuiltinSort SortLevelUniv)
  , (builtinLevelZero                        |-> BuiltinPrim PrimLevelZero (const $ return ()))
  , (builtinLevelSuc                         |-> BuiltinPrim PrimLevelSuc (const $ return ()))
  , (builtinLevelMax                         |-> BuiltinPrim PrimLevelMax verifyMax)
  , (builtinSet                              |-> BuiltinSort SortSet)
  , (builtinProp                             |-> BuiltinSort SortProp)
  , (builtinSetOmega                         |-> BuiltinSort SortSetOmega)
  , (builtinSSetOmega                        |-> BuiltinSort SortStrictSetOmega)
  , (builtinStrictSet                        |-> BuiltinSort SortStrictSet)
  , (builtinAgdaClause                       |-> BuiltinData tset [builtinAgdaClauseClause, builtinAgdaClauseAbsurd])
  , (builtinAgdaClauseClause                 |-> BuiltinDataCons (ttelescope --> tlist (targ tpat) --> tterm --> tclause))
  , (builtinAgdaClauseAbsurd                 |-> BuiltinDataCons (ttelescope --> tlist (targ tpat) --> tclause))
  , (builtinAgdaDefinition                   |-> BuiltinData tset [builtinAgdaDefinitionFunDef
                                                                  ,builtinAgdaDefinitionDataDef
                                                                  ,builtinAgdaDefinitionDataConstructor
                                                                  ,builtinAgdaDefinitionRecordDef
                                                                  ,builtinAgdaDefinitionPostulate
                                                                  ,builtinAgdaDefinitionPrimitive])
  , (builtinAgdaDefinitionFunDef             |-> BuiltinDataCons (tlist tclause --> tdefn))
  , (builtinAgdaDefinitionDataDef            |-> BuiltinDataCons (tnat --> tlist tqname --> tdefn))
  , (builtinAgdaDefinitionDataConstructor    |-> BuiltinDataCons (tqname --> tdefn))
  , (builtinAgdaDefinitionRecordDef          |-> BuiltinDataCons (tqname --> tlist (targ tqname) --> tdefn))
  , (builtinAgdaDefinitionPostulate          |-> BuiltinDataCons tdefn)
  , (builtinAgdaDefinitionPrimitive          |-> BuiltinDataCons tdefn)
  , builtinAgdaTCM                           |-> builtinPostulate (hPi "a" tlevel $ tsetL 0 --> tsetL 0)
  , builtinAgdaTCMReturn                     |-> builtinPostulate (hPi "a" tlevel  $
                                                                   hPi "A" (tsetL 0) $
                                                                   elV 1 (varM 0) --> tTCM 1 (varM 0))
  , builtinAgdaTCMBind                       |-> builtinPostulate (hPi "a" tlevel  $ hPi "b" tlevel $
                                                                   hPi "A" (tsetL 1) $ hPi "B" (tsetL 1) $
                                                                   tTCM 3 (varM 1) --> (elV 3 (varM 1) --> tTCM 2 (varM 0)) --> tTCM 2 (varM 0))
  , builtinAgdaTCMUnify                      |-> builtinPostulate (tterm --> tterm --> tTCM_ primUnit)
  , builtinAgdaTCMTypeError                  |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ tlist terrorpart --> tTCM 1 (varM 0))
  , builtinAgdaTCMInferType                  |-> builtinPostulate (tterm --> tTCM_ primAgdaTerm)
  , builtinAgdaTCMCheckType                  |-> builtinPostulate (tterm --> ttype --> tTCM_ primAgdaTerm)
  , builtinAgdaTCMNormalise                  |-> builtinPostulate (tterm --> tTCM_ primAgdaTerm)
  , builtinAgdaTCMReduce                     |-> builtinPostulate (tterm --> tTCM_ primAgdaTerm)
  , builtinAgdaTCMCatchError                 |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $
                                                                   tTCM 1 (varM 0) --> tTCM 1 (varM 0) --> tTCM 1 (varM 0))
  , builtinAgdaTCMGetContext                 |-> builtinPostulate (tTCM_ (unEl <$> ttelescope))
  , builtinAgdaTCMExtendContext              |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $
                                                                   tstring --> targ ttype --> tTCM 1 (varM 0) --> tTCM 1 (varM 0))
  , builtinAgdaTCMInContext                  |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $
                                                                   ttelescope --> tTCM 1 (varM 0) --> tTCM 1 (varM 0))
  , builtinAgdaTCMFreshName                  |-> builtinPostulate (tstring --> tTCM_ primQName)
  , builtinAgdaTCMDeclareDef                 |-> builtinPostulate (targ tqname --> ttype --> tTCM_ primUnit)
  , builtinAgdaTCMDeclarePostulate           |-> builtinPostulate (targ tqname --> ttype --> tTCM_ primUnit)
  , builtinAgdaTCMDeclareData                |-> builtinPostulate (tqname --> tnat --> ttype --> tTCM_ primUnit)
  , builtinAgdaTCMDefineData                 |-> builtinPostulate (tqname --> tlist (tpair primLevelZero primLevelZero tqname ttype) --> tTCM_ primUnit)
  , builtinAgdaTCMDefineFun                  |-> builtinPostulate (tqname --> tlist tclause --> tTCM_ primUnit)
  , builtinAgdaTCMGetType                    |-> builtinPostulate (tqname --> tTCM_ primAgdaTerm)
  , builtinAgdaTCMGetDefinition              |-> builtinPostulate (tqname --> tTCM_ primAgdaDefinition)
  , builtinAgdaTCMQuoteTerm                  |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ elV 1 (varM 0) --> tTCM_ primAgdaTerm)
  , builtinAgdaTCMUnquoteTerm                |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ tterm --> tTCM 1 (varM 0))
  , builtinAgdaTCMQuoteOmegaTerm             |-> builtinPostulate (hPi "A" tsetOmega $ (elInf $ varM 0) --> tTCM_ primAgdaTerm)
  , builtinAgdaTCMBlockOnMeta                |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ tmeta --> tTCM 1 (varM 0))
  , builtinAgdaTCMCommit                     |-> builtinPostulate (tTCM_ primUnit)
  , builtinAgdaTCMIsMacro                    |-> builtinPostulate (tqname --> tTCM_ primBool)
  , builtinAgdaTCMWithNormalisation          |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ tbool --> tTCM 1 (varM 0) --> tTCM 1 (varM 0))
  , builtinAgdaTCMWithReconstructed          |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ tbool --> tTCM 1 (varM 0) --> tTCM 1 (varM 0))
  , builtinAgdaTCMWithExpandLast             |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ tbool --> tTCM 1 (varM 0) --> tTCM 1 (varM 0))
  , builtinAgdaTCMWithReduceDefs             |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ (tpair primLevelZero primLevelZero tbool (tlist tqname)) --> tTCM 1 (varM 0) --> tTCM 1 (varM 0))
  , builtinAgdaTCMAskNormalisation           |-> builtinPostulate (tTCM_ (unEl <$> tbool))
  , builtinAgdaTCMAskReconstructed           |-> builtinPostulate (tTCM_ (unEl <$> tbool))
  , builtinAgdaTCMAskExpandLast              |-> builtinPostulate (tTCM_ (unEl <$> tbool))
  , builtinAgdaTCMAskReduceDefs              |-> builtinPostulate (tTCM_ (unEl <$> (tpair primLevelZero primLevelZero tbool (tlist tqname))))
  , builtinAgdaTCMFormatErrorParts           |-> builtinPostulate (tlist terrorpart --> tTCM_ primString)
  , builtinAgdaTCMDebugPrint                 |-> builtinPostulate (tstring --> tnat --> tlist terrorpart --> tTCM_ primUnit)

  , builtinAgdaTCMNoConstraints              |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $ tTCM 1 (varM 0) --> tTCM 1 (varM 0))
  , builtinAgdaTCMRunSpeculative             |-> builtinPostulate (hPi "a" tlevel $ hPi "A" (tsetL 0) $
                                                                   tTCM 1 (primSigma <#> varM 1 <#> primLevelZero <@> varM 0 <@> (Lam defaultArgInfo . Abs "_" <$> primBool)) --> tTCM 1 (varM 0))
  , builtinAgdaTCMExec                       |-> builtinPostulate (tstring --> tlist tstring --> tstring -->
                                                                   tTCM_ (primSigma <#> primLevelZero <#> primLevelZero <@> primNat <@>
                                                                          (Lam defaultArgInfo . Abs "_" <$> (primSigma <#> primLevelZero <#> primLevelZero <@> primString <@>
                                                                           (Lam defaultArgInfo . Abs "_" <$> primString)))))
  , builtinAgdaTCMGetInstances               |-> builtinPostulate (tmeta --> tTCM_ (list primAgdaTerm))
  , builtinAgdaTCMPragmaForeign              |-> builtinPostulate (tstring --> tstring --> tTCM_ primUnit)
  , builtinAgdaTCMPragmaCompile              |-> builtinPostulate (tstring --> tqname --> tstring --> tTCM_ primUnit)
  ]
  where
        (|->) = BuiltinInfo

        v0 :: TCM Term
        v0 = varM 0

        tv0 :: TCM Type
        tv0 = el v0

        arg :: TCM Term -> TCM Term
        arg t = primArg <@> t

        elV x a = El (varSort x) <$> a

        tsetL l    = return $ sort (varSort l)
        tsetOmega  = return $ sort $ Inf IsFibrant 0
        tlevel     = el primLevel
        tlist x    = el $ list (fmap unEl x)
        tmaybe x   = el $ tMaybe (fmap unEl x)
        tpair lx ly x y = el $ primSigma
                            <#> lx
                            <#> ly
                            <@> fmap unEl x
                            <@> (Lam defaultArgInfo . NoAbs "_" <$> fmap unEl y)
        targ x     = el (arg (fmap unEl x))
        tabs x     = el (primAbs <@> fmap unEl x)
        targs      = el (list (arg primAgdaTerm))
        tterm      = el primAgdaTerm
        terrorpart = el primAgdaErrorPart
        tnat       = el primNat
        tword64    = el primWord64
        tinteger   = el primInteger
        tfloat     = el primFloat
        tchar      = el primChar
        tstring    = el primString
        tqname     = el primQName
        tmeta      = el primAgdaMeta
        tsize      = El sSizeUniv <$> primSize
        tbool      = el primBool
        thiding    = el primHiding
        trelevance = el primRelevance
        tquantity  = el primQuantity
        tmodality  = el primModality
        tassoc     = el primAssoc
        tprec      = el primPrecedence
        tfixity    = el primFixity
--        tcolors    = el (list primAgdaTerm) -- TODO guilhem
        targinfo   = el primArgInfo
        ttype      = el primAgdaTerm
        tsort      = el primAgdaSort
        tdefn      = el primAgdaDefinition
        tliteral   = el primAgdaLiteral
        tpat       = el primAgdaPattern
        tclause    = el primAgdaClause
        ttelescope = tlist (tpair primLevelZero primLevelZero tstring (targ ttype))
        tTCM l a   = elV l (primAgdaTCM <#> varM l <@> a)
        tTCM_ a    = el (primAgdaTCM <#> primLevelZero <@> a)
        tinterval  = El IntervalUniv <$> primInterval

        verifyPlus plus =
            verify ["n","m"] $ \(@@) zero suc (==) (===) choice -> do
                let m = var 0
                    n = var 1
                    x + y = plus @@ x @@ y

                -- We allow recursion on any argument
                choice
                    [ do n + zero  == n
                         n + suc m == suc (n + m)
                    , do suc n + m == suc (n + m)
                         zero  + m == m
                    ]

        verifyMinus minus =
            verify ["n","m"] $ \(@@) zero suc (==) (===) choice -> do
                let m = var 0
                    n = var 1
                    x - y = minus @@ x @@ y

                -- We allow recursion on any argument
                zero  - zero  == zero
                zero  - suc m == zero
                suc n - zero  == suc n
                suc n - suc m == (n - m)

        verifyTimes times = do
            plus <- primNatPlus
            verify ["n","m"] $ \(@@) zero suc (==) (===) choice -> do
                let m = var 0
                    n = var 1
                    x + y = plus  @@ x @@ y
                    x * y = times @@ x @@ y

                choice
                    [ do n * zero == zero
                         choice [ (n * suc m) == (n + (n * m))
                                , (n * suc m) == ((n * m) + n)
                                ]
                    , do zero * n == zero
                         choice [ (suc n * m) == (m + (n * m))
                                , (suc n * m) == ((n * m) + m)
                                ]
                    ]

        verifyDivSucAux dsAux =
            verify ["k","m","n","j"] $ \(@@) zero suc (==) (===) choice -> do
                let aux k m n j = dsAux @@ k @@ m @@ n @@ j
                    k           = var 0
                    m           = var 1
                    n           = var 2
                    j           = var 3

                aux k m zero    j       == k
                aux k m (suc n) zero    == aux (suc k) m n m
                aux k m (suc n) (suc j) == aux k m n j

        verifyModSucAux dsAux =
            verify ["k","m","n","j"] $ \(@@) zero suc (==) (===) choice -> do
                let aux k m n j = dsAux @@ k @@ m @@ n @@ j
                    k           = var 0
                    m           = var 1
                    n           = var 2
                    j           = var 3

                aux k m zero    j       == k
                aux k m (suc n) zero    == aux zero m n m
                aux k m (suc n) (suc j) == aux (suc k) m n j

        verifyEquals eq =
            verify ["n","m"] $ \(@@) zero suc (==) (===) choice -> do
            true  <- primTrue
            false <- primFalse
            let x == y = eq @@ x @@ y
                m      = var 0
                n      = var 1
            (zero  == zero ) === true
            (suc n == suc m) === (n == m)
            (suc n == zero ) === false
            (zero  == suc n) === false

        verifyLess leq =
            verify ["n","m"] $ \(@@) zero suc (==) (===) choice -> do
            true  <- primTrue
            false <- primFalse
            let x < y = leq @@ x @@ y
                m     = var 0
                n     = var 1
            (n     < zero)  === false
            (suc n < suc m) === (n < m)
            (zero  < suc m) === true

        verifyMax maxV = return ()  -- TODO: make max a postulate

        verify xs = verify' primNat primZero primSuc xs

        verify' ::  TCM Term -> TCM Term -> TCM Term ->
                    [String] -> ( (Term -> Term -> Term) -> Term -> (Term -> Term) ->
                                (Term -> Term -> TCM ()) ->
                                (Term -> Term -> TCM ()) ->
                                ([TCM ()] -> TCM ()) -> TCM a) -> TCM a
        verify' pNat pZero pSuc xs f = do
            nat  <- El (mkType 0) <$> pNat
            zero <- pZero
            s    <- pSuc
            let x == y  = noConstraints $ equalTerm nat x y
                -- Andreas: 2013-10-21 I put primBool here on the inside
                -- since some Nat-builtins do not require Bool-builtins
                x === y = do bool <- El (mkType 0) <$> primBool
                             noConstraints $ equalTerm bool x y
                suc n  = s `apply1` n
                choice = foldr1 (\x y -> x `catchError` \_ -> y)
            xs <- mapM freshName_ xs
            addContext (xs, domFromArg $ defaultArg nat) $ f apply1 zero suc (==) (===) choice

        verifyPath :: Term -> Type -> TCM ()
        verifyPath path t = do
          let hlam n t = glam (setHiding Hidden defaultArgInfo) n t
          noConstraints $ equalTerm t path =<< runNamesT [] (
            hlam "l" $ \ l -> hlam "A" $ \ bA -> cl primPathP <#> l <@> lam "i" (\ _ -> bA))

-- | Checks that builtin with name @b : String@ of type @t : Term@
--   is a data type or inductive record with @n : Int@ constructors.
--   Returns the name of the data/record type.
inductiveCheck :: BuiltinId -> Int -> Term -> TCM (QName, Definition)
inductiveCheck b n t = do
  caseMaybeM (headSymbol t) no $ \q -> do
      def <- getConstInfo q
      let yes = return (q, def)
      case theDef def of
        Datatype { dataCons = cs }
          | length cs == n -> yes
          | otherwise      -> no
        Record { recInduction = ind } | n == 1 && ind /= Just CoInductive -> yes
        _ -> no
  where
  headSymbol :: Term -> TCM (Maybe QName)
  headSymbol t = reduce t >>= \case
    Def q _ -> return $ Just q
    Lam _ b -> headSymbol $ lazyAbsApp b __DUMMY_TERM__
    _       -> return Nothing

  no
    | n == 1 = typeError $ GenericError $ unwords
        [ "The builtin", getBuiltinId b
        , "must be a datatype with a single constructor"
        , "or an (inductive) record type"
        ]
    | otherwise = typeError $ GenericError $ unwords
        [ "The builtin", getBuiltinId b
        , "must be a datatype with", show n
        , "constructors"
        ]

-- | @bindPostulatedName builtin q m@ checks that @q@ is a postulated
-- name, and binds the builtin @builtin@ to the term @m q def@,
-- where @def@ is the current 'Definition' of @q@.

bindPostulatedName ::
  BuiltinId -> ResolvedName -> (QName -> Definition -> TCM Term) -> TCM ()
bindPostulatedName builtin x m = do
  q   <- getName x
  def <- getConstInfo q
  case theDef def of
    Axiom {} -> bindBuiltinName builtin =<< m q def
    _        -> err
  where
  err :: forall m a. MonadTCError m => m a
  err = typeError $ GenericError $
          "The argument to BUILTIN " ++ getBuiltinId builtin ++
          " must be a postulated name"
  getName = \case
    DefinedName _ d NoSuffix -> return $ anameName d
    _ -> err

addHaskellPragma :: QName -> String -> TCM ()
addHaskellPragma = addPragma ghcBackendName

bindAndSetHaskellCode :: BuiltinId -> String -> Term -> TCM ()
bindAndSetHaskellCode b hs t = do
  d <- fromMaybe __IMPOSSIBLE__ <$> getDef t
  bindBuiltinName b t
  addHaskellPragma d hs

bindBuiltinBool :: Term -> TCM ()
bindBuiltinBool = bindAndSetHaskellCode builtinBool "= type Bool"

-- | Check that we're not trying to bind true and false to the same
-- constructor.
checkBuiltinBool :: TCM ()
checkBuiltinBool = do
  true  <- getBuiltin' builtinTrue
  false <- getBuiltin' builtinFalse
  when (true == false) $
    genericError "Cannot bind TRUE and FALSE to the same constructor"

bindBuiltinInt :: Term -> TCM ()
bindBuiltinInt = bindAndSetHaskellCode builtinInteger "= type Integer"

bindBuiltinNat :: Term -> TCM ()
bindBuiltinNat t = do
  bindBuiltinData builtinNat t
  name <- fromMaybe __IMPOSSIBLE__ <$> getDef t
  addHaskellPragma name "= type Integer"

-- | Only use for datatypes with distinct arities of constructors.
--   Binds the constructors together with the datatype.
bindBuiltinData :: BuiltinId -> Term -> TCM ()
bindBuiltinData s t = do
  bindBuiltinName s t
  name <- fromMaybe __IMPOSSIBLE__ <$> getDef t
  Datatype{ dataCons = cs } <- theDef <$> getConstInfo name
  let getArity c = do
        Constructor{ conArity = a } <- theDef <$> getConstInfo c
        return a
      getBuiltinArity (BuiltinDataCons t) = arity <$> t
      getBuiltinArity _ = __IMPOSSIBLE__
      sortByM f xs = map fst . sortBy (compare `on` snd) . zip xs <$> mapM f xs
  -- Order constructurs by arity
  cs <- sortByM getArity cs
  -- Do the same for the builtins
  let bcis = fromMaybe __IMPOSSIBLE__ $ do
        BuiltinData _ bcs <- builtinDesc <$> findBuiltinInfo s
        mapM findBuiltinInfo bcs
  bcis <- sortByM (getBuiltinArity . builtinDesc) bcis
  unless (length cs == length bcis) __IMPOSSIBLE__  -- we already checked this
  zipWithM_ (\ c bci -> bindBuiltinInfo bci (A.Con $ unambiguous $ setRange (getRange name) c)) cs bcis

bindBuiltinUnit :: Term -> TCM ()
bindBuiltinUnit t = do
  unit <- fromMaybe __IMPOSSIBLE__ <$> getDef t
  def <- theDef <$> getConstInfo unit
  case def of
    Record { recFields = [], recConHead = con } -> do
      bindBuiltinName builtinUnit t
      bindBuiltinName builtinUnitUnit (Con con ConOSystem [])
    _ -> genericError "Builtin UNIT must be a singleton record type"

bindBuiltinSigma :: Term -> TCM ()
bindBuiltinSigma t = do
  sigma <- fromMaybe __IMPOSSIBLE__ <$> getDef t
  def <- theDef <$> getConstInfo sigma
  case def of
    Record { recFields = [fst,snd], recConHead = con } -> do
      bindBuiltinName builtinSigma t
    _ -> genericError "Builtin SIGMA must be a record type with two fields"

-- | Bind BUILTIN EQUALITY and BUILTIN REFL.
bindBuiltinEquality :: ResolvedName -> TCM ()
bindBuiltinEquality x = do
  (v, _t) <- inferExpr (A.nameToExpr x)

  -- Equality needs to be a data type with 1 constructor
  (eq, def) <- inductiveCheck builtinEquality 1 v

  -- Check that the type is the type of a polymorphic relation, i.e.,
  -- Γ → (A : Set _) → A → A → Set _
  TelV eqTel eqCore <- telView $ defType def
  let no = genericError "The type of BUILTIN EQUALITY must be a polymorphic relation"

  -- The target is a sort since eq is a data type.
  unless (isJust $ isSort $ unEl eqCore) __IMPOSSIBLE__

  -- The types of the last two arguments must be the third-last argument
  unless (natSize eqTel >= 3) no
  let (a, b) = fromMaybe __IMPOSSIBLE__ $ last2 $ telToList eqTel
  [a,b] <- reduce $ map (unEl . snd . unDom) [a,b]
  unless (deBruijnView a == Just 0) no
  unless (deBruijnView b == Just 1) no

  -- Get the single constructor.
  case theDef def of
    Datatype { dataCons = [c] } -> do
      bindBuiltinName builtinEquality v

      -- Check type of REFL.  It has to be of the form
      -- pars → (x : A) → Eq ... x x

      -- Check the arguments
      cdef <- getConstInfo c
      TelV conTel conCore <- telView $ defType cdef
      ts <- reduce $ map (unEl . snd . unDom) $ drop (conPars $ theDef cdef) $ telToList conTel
      -- After dropping the parameters, there should be maximally one argument.
      unless (length ts <= 1) wrongRefl
      unless (all ((Just 0 ==) . deBruijnView) ts) wrongRefl

      -- Check the target
      case unEl conCore of
        Def _ es -> do
          let vs = map unArg $ fromMaybe __IMPOSSIBLE__ $ allApplyElims es
          (a,b) <- reduce $ fromMaybe __IMPOSSIBLE__ $ last2 vs
          unless (deBruijnView a == Just 0) wrongRefl
          unless (deBruijnView b == Just 0) wrongRefl
          bindBuiltinName builtinRefl (Con (ConHead c IsData Inductive []) ConOSystem [])
        _ -> __IMPOSSIBLE__
    _ -> genericError "Builtin EQUALITY must be a data type with a single constructor"
  where
  wrongRefl = genericError "Wrong type of constructor of BUILTIN EQUALITY"

bindBuiltinInfo :: BuiltinInfo -> A.Expr -> TCM ()
bindBuiltinInfo (BuiltinInfo s d) e = do
    case d of
      BuiltinData t cs -> do
        v <- checkExpr e =<< t
        unless (s == builtinUnit) $ do
          void $ inductiveCheck s (length cs) v
        if | s == builtinEquality -> __IMPOSSIBLE__ -- bindBuiltinEquality v
           | s == builtinBool     -> bindBuiltinBool     v
           | s == builtinNat      -> bindBuiltinNat      v
           | s == builtinInteger  -> bindBuiltinInt      v
           | s == builtinUnit     -> bindBuiltinUnit     v
           | s == builtinSigma    -> bindBuiltinSigma    v
           | s == builtinList     -> bindBuiltinData s   v
           | s == builtinMaybe    -> bindBuiltinData s   v
           | otherwise            -> bindBuiltinName s   v

      BuiltinDataCons t -> do

        let name (Lam h b)  = name (absBody b)
            name (Con c ci _) = Con c ci []
            name _          = __IMPOSSIBLE__

        v0 <- checkExpr e =<< t

        case e of
          A.Con{} -> return ()
          _       -> typeError $ BuiltinMustBeConstructor s e

        let v@(Con h _ []) = name v0

        bindBuiltinName s v

        when (s `elem` [builtinFalse, builtinTrue]) checkBuiltinBool

      BuiltinPrim pfname axioms -> do
        case e of
          A.Def qx -> do

            PrimImpl t pf <- lookupPrimitiveFunction pfname
            v <- checkExpr e t

            axioms v

            info <- getConstInfo qx
            let cls = defClauses info
                a   = defAbstract info
                o   = defOpaque info
                mcc = defCompiled info
                inv = defInverse info
            bindPrimitive pfname $ pf { primFunName = qx }
            addConstant qx $ info { theDef = Primitive { primAbstr    = a
                                                       , primName     = pfname
                                                       , primClauses  = cls
                                                       , primInv      = inv
                                                       , primCompiled = mcc
                                                       , primOpaque   = o
                                                       } }

            -- needed? yes, for checking equations for mul
            bindBuiltinName s v

          _ -> typeError $ GenericError $ "Builtin " ++ getBuiltinId s ++ " must be bound to a function"

      BuiltinSort{} -> __IMPOSSIBLE__ -- always a "BuiltinNoDef"

      BuiltinPostulate rel t -> do
        t' <- t
        v <- applyRelevanceToContext rel $ checkExpr e t'
        let err = typeError $ GenericError $
                    "The argument to BUILTIN " ++ getBuiltinId s ++ " must be a postulated name"
        case e of
          A.Def q -> do
            def <- getConstInfo q
            case theDef def of
              Axiom {} -> do
                builtinSizeHook s q t'
                -- And compilation pragmas for base types
                when (s == builtinLevel)  $ setConstTranspAxiom q >> addHaskellPragma q "= type ()"
                when (s == builtinChar)   $ setConstTranspAxiom q >> addHaskellPragma q "= type Char"
                when (s == builtinString) $ setConstTranspAxiom q >> addHaskellPragma q "= type Data.Text.Text"
                when (s == builtinFloat)  $ setConstTranspAxiom q >> addHaskellPragma q "= type Double"
                when (s == builtinWord64) $ setConstTranspAxiom q >> addHaskellPragma q "= type MAlonzo.RTE.Word64"
                when (s == builtinPathP)  $ builtinPathPHook q
                bindBuiltinName s v
              _        -> err
          _ -> err

      BuiltinUnknown mt f -> do
        (v, t) <- caseMaybe mt (inferExpr e) $ \ tcmt -> do
          t <- tcmt
          (,t) <$> checkExpr e t
        f v t
        if | s == builtinRewrite -> runMaybeT (getQNameFromTerm v) >>= \case
              Nothing -> genericError "Invalid rewrite relation"
              Just q  -> bindBuiltinRewriteRelation q
           | otherwise           -> bindBuiltinName s v

setConstTranspAxiom :: QName -> TCM ()
setConstTranspAxiom q =
  modifySignature $ updateDefinition q $ updateTheDef (const $ constTranspAxiom)

builtinPathPHook :: QName -> TCM ()
builtinPathPHook q =
      modifySignature $ updateDefinition q
      $ updateDefPolarity       id
      . updateDefArgOccurrences (const [Unused,StrictPos,Mixed,Mixed])

builtinIdHook :: QName -> TCM ()
builtinIdHook q = do
      modifySignature $ updateDefinition q
        $ updateDefPolarity       id
        . updateDefArgOccurrences (const [Unused,StrictPos,Mixed,Mixed])
      modifySignature $ updateDefinition q
        $ updateTheDef (\ def@Datatype{} -> def { dataPars = 3, dataIxs = 1})

builtinReflIdHook :: QName -> TCM ()
builtinReflIdHook q = do
      modifySignature $ updateDefinition q
        $ updateTheDef (\ def@Constructor{} -> def { conPars = 3, conArity = 0})

-- | Bind a builtin thing to an expression.
bindBuiltin :: BuiltinId -> ResolvedName -> TCM ()
bindBuiltin b x = do
  unlessM ((0 ==) <$> getContextSize) $ do
    -- Andreas, 2017-11-01, issue #2824
    -- Only raise an error if the name for the builtin is defined in a parametrized module.
    let
      failure :: forall m a. MonadTCError m => m a
      failure = typeError $ BuiltinInParameterisedModule b
    -- Get the non-empty list of AbstractName for x
    xs <- case x of
      VarName{}            -> failure
      DefinedName _ x NoSuffix -> return $ x :| []
      DefinedName _ x Suffix{} -> failure
      FieldName xs         -> return xs
      ConstructorName _ xs -> return xs
      PatternSynResName xs -> failure
      UnknownName          -> failure
    -- For ambiguous names, we check all of their definitions:
    unlessM (allM xs $ null <.> lookupSection . qnameModule . anameName) $
      failure
  -- Since the name was define in a parameter-free context, we can switch to the empty context.
  -- (And we should!)
  inTopContext $ do
  if | b == builtinRefl  -> warning $ OldBuiltin b builtinEquality
     | b == builtinZero  -> now builtinNat b
     | b == builtinSuc   -> now builtinNat b
     | b == builtinNil   -> now builtinList b
     | b == builtinCons  -> now builtinList b
     | b == builtinInf   -> bindBuiltinInf x
     | b == builtinSharp -> bindBuiltinSharp x
     | b == builtinFlat  -> bindBuiltinFlat x
     | b == builtinEquality -> bindBuiltinEquality x
     | Just i <- findBuiltinInfo b -> bindBuiltinInfo i (A.nameToExpr x)
     | otherwise -> typeError $ NoSuchBuiltinName (getBuiltinId b)
  where
    now new b = warning $ OldBuiltin b new

isUntypedBuiltin :: BuiltinId -> Bool
isUntypedBuiltin = hasElem [ builtinFromNat, builtinFromNeg, builtinFromString ]

bindUntypedBuiltin :: BuiltinId -> ResolvedName -> TCM ()
bindUntypedBuiltin b = \case
  DefinedName _ x NoSuffix -> bind x
  DefinedName _ x Suffix{} -> wrong
  FieldName (x :| [])  -> bind x
  FieldName (x :| _)   -> amb x
  VarName _x _bnd      -> wrong
  UnknownName          -> wrong
  ConstructorName _ xs -> err xs
  PatternSynResName xs -> err xs
  where
  bind x = bindBuiltinName b (Def (anameName x) [])
  wrong  = genericError $ "The argument to BUILTIN " ++ getBuiltinId b ++ " must be a defined name"
  amb x  = genericDocError =<< do text "Name " <+> prettyTCM x <+> text " is ambiguous"
  err (x :| xs1)
    | null xs1  = wrong
    | otherwise = amb x

-- | Bind a builtin thing to a new name.
--
-- Since their type is closed, it does not matter whether we are in a
-- parameterized module when we declare them.
-- We simply ignore the parameters.
bindBuiltinNoDef :: BuiltinId -> A.QName -> TCM ()
bindBuiltinNoDef b q = inTopContext $ do
  when (b `elem` sizeBuiltins) $ unlessM sizedTypesOption $
    genericError $ "Cannot declare size BUILTIN " ++ getBuiltinId b ++ " with option --no-sized-types"
  case builtinDesc <$> findBuiltinInfo b of

    Just (BuiltinPostulate rel mt) -> do
      -- We start by adding the corresponding postulate
      t   <- mt
      fun <- emptyFunctionData
      addConstant' q (setRelevance rel defaultArgInfo) q t (def fun)
      -- And we then *modify* the definition based on our needs:
      -- We add polarity information for SIZE-related definitions
      builtinSizeHook b q t
      -- Finally, bind the BUILTIN in the environment.
      bindBuiltinName b $ Def q []
      where
        -- Andreas, 2015-02-14
        -- Special treatment of SizeUniv, should maybe be a primitive.
        def fun
            | b == builtinSizeUniv = FunctionDefn $ fun
                { _funClauses    = [ (empty :: Clause) { clauseBody = Just $ Sort sSizeUniv } ]
                , _funCompiled   = Just (CC.Done [] $ Sort sSizeUniv)
                , _funMutual     = Just []
                , _funTerminates = Just True
                }
            | otherwise = defaultAxiom

    Just (BuiltinPrim name axioms) -> do
      PrimImpl t pf <- lookupPrimitiveFunction name
      bindPrimitive name $ pf { primFunName = q }
      let v   = Def q []
          def = Primitive { primAbstr    = ConcreteDef
                          , primName     = name
                          , primClauses  = []
                          , primInv      = NotInjective
                          , primCompiled = Just (CC.Done [] $ Def q [])
                          , primOpaque   = TransparentDef
                          }
      addConstant' q defaultArgInfo q t def
      axioms v
      bindBuiltinName b v

    Just (BuiltinDataCons mt) -> do
      t       <- mt
      d       <- return $! getPrimName $ unEl t
      erasure <- optErasure <$> pragmaOptions
      let
        ch = ConHead q IsData Inductive []
        def = Constructor
              { conPars   = 0   -- Andrea TODO: fix zeros
              , conArity  = 0
              , conSrcCon = ch
              , conData   = d
              , conAbstr  = ConcreteDef
              , conInd    = Inductive
              , conComp   = emptyCompKit
              , conProj   = Nothing
              , conForced = []
              , conErased = Nothing
              , conErasure = erasure
              }
      addConstant' q defaultArgInfo q t def
      addDataCons d [q]

      when (b == builtinReflId)     $ builtinReflIdHook q

      bindBuiltinName b $ Con ch ConOSystem []

    Just (BuiltinData mt cs) -> do
      t <- mt
      addConstant' q defaultArgInfo q t (def t)
      when (b == builtinId)     $ builtinIdHook q
      bindBuiltinName b $ Def q []
      where
        def t = Datatype
              { dataPars       = 0
              , dataIxs        = 0
              , dataClause     = Nothing
              , dataCons       = []     -- Constructors are added later
              , dataSort       = getSort t
              , dataAbstr      = ConcreteDef
              , dataMutual     = Nothing
              , dataPathCons   = []
              , dataTranspIx   = Nothing -- Id has custom transp def.
              , dataTransp     = Nothing
              }

    Just (BuiltinSort builtinSort) -> do
      let s = case builtinSort of
                SortSet -> mkType 0
                SortProp -> mkProp 0
                SortStrictSet -> mkSSet 0
                SortSetOmega -> Inf IsFibrant 0
                SortStrictSetOmega -> Inf IsStrict 0
                SortIntervalUniv -> IntervalUniv
                SortLevelUniv -> LevelUniv
          def = PrimitiveSort builtinSort s
      -- Check for the cubical flag if the sort requries it
      case builtinSort of
        SortIntervalUniv -> requireCubical CErased ""
        _ -> return ()
      addConstant' q defaultArgInfo q (sort $ univSort s) def
      bindBuiltinName b $ Def q []

    Just{}  -> __IMPOSSIBLE__
    Nothing -> __IMPOSSIBLE__ -- typeError $ NoSuchBuiltinName b


builtinKindOfName :: BuiltinId -> Maybe KindOfName
builtinKindOfName = distinguish <.> findBuiltinInfo
  where
  distinguish d = case builtinDesc d of
    BuiltinDataCons{}  -> ConName
    BuiltinData{}      -> DataName       -- Andreas, 2020-04-13: Crude.  Could be @RecName@.
    BuiltinPrim{}      -> PrimName
    BuiltinPostulate{} -> AxiomName
    BuiltinSort{}      -> PrimName
    BuiltinUnknown{}   -> OtherDefName
