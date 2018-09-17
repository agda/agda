{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Builtin where

import Control.Monad.State
import Control.Monad.Trans.Maybe

import qualified Data.Map as Map

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Internal as I
import Agda.TypeChecking.Monad.Base
-- import Agda.TypeChecking.Functions  -- LEADS TO IMPORT CYCLE
import Agda.TypeChecking.Substitute

import Agda.Utils.Except
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Maybe
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

class (Functor m, Applicative m, Monad m) => HasBuiltins m where
  getBuiltinThing :: String -> m (Maybe (Builtin PrimFun))

instance HasBuiltins m => HasBuiltins (MaybeT m) where
  getBuiltinThing b = lift $ getBuiltinThing b

instance HasBuiltins m => HasBuiltins (ExceptT e m) where
  getBuiltinThing b = lift $ getBuiltinThing b

instance HasBuiltins m => HasBuiltins (StateT s m) where
  getBuiltinThing b = lift $ getBuiltinThing b

litType :: Literal -> TCM Type
litType l = case l of
  LitNat _ n    -> do
    _ <- primZero
    when (n > 0) $ void $ primSuc
    el <$> primNat
  LitWord64 _ _ -> el <$> primWord64
  LitFloat _ _  -> el <$> primFloat
  LitChar _ _   -> el <$> primChar
  LitString _ _ -> el <$> primString
  LitQName _ _  -> el <$> primQName
  LitMeta _ _ _ -> el <$> primAgdaMeta
  where
    el t = El (mkType 0) t

instance MonadIO m => HasBuiltins (TCMT m) where
  getBuiltinThing b = liftM2 mplus (Map.lookup b <$> useTC stLocalBuiltins)
                      (Map.lookup b <$> useTC stImportedBuiltins)

setBuiltinThings :: BuiltinThings PrimFun -> TCM ()
setBuiltinThings b = stLocalBuiltins `setTCLens` b

bindBuiltinName :: String -> Term -> TCM ()
bindBuiltinName b x = do
  builtin <- getBuiltinThing b
  case builtin of
    Just (Builtin y) -> typeError $ DuplicateBuiltinBinding b y x
    Just (Prim _)    -> typeError $ NoSuchBuiltinName b
    Nothing          -> stLocalBuiltins `modifyTCLens` Map.insert b (Builtin x)

bindPrimitive :: String -> PrimFun -> TCM ()
bindPrimitive b pf = do
  builtin <- useTC stLocalBuiltins
  setBuiltinThings $ Map.insert b (Prim pf) builtin

getBuiltin :: String -> TCM Term
getBuiltin x =
  fromMaybeM (typeError $ NoBindingForBuiltin x) $ getBuiltin' x

getBuiltin' :: HasBuiltins m => String -> m (Maybe Term)
getBuiltin' x = do
    builtin <- getBuiltinThing x
    case builtin of
        Just (Builtin t) -> return $ Just $ killRange t
        _                -> return Nothing

getPrimitive' :: HasBuiltins m => String -> m (Maybe PrimFun)
getPrimitive' x = (getPrim =<<) <$> getBuiltinThing x
  where
    getPrim (Prim pf) = return pf
    getPrim _         = Nothing

getPrimitive :: String -> TCM PrimFun
getPrimitive x =
  fromMaybeM (typeError $ NoSuchPrimitiveFunction x) $ getPrimitive' x

getPrimitiveTerm :: String -> TCM Term
getPrimitiveTerm x = (`Def` []) <$> primFunName <$> getPrimitive x

getPrimitiveTerm' :: HasBuiltins m => String -> m (Maybe Term)
getPrimitiveTerm' x = fmap (`Def` []) <$> getPrimitiveName' x

getTerm' :: HasBuiltins m => String -> m (Maybe Term)
getTerm' x = mplus <$> getBuiltin' x <*> getPrimitiveTerm' x

getName' :: HasBuiltins m => String -> m (Maybe QName)
getName' x = mplus <$> getBuiltinName' x <*> getPrimitiveName' x


-- | Rewrite a literal to constructor form if possible.
constructorForm :: Term -> TCM Term
constructorForm v = constructorForm' primZero primSuc v

constructorForm' :: Applicative m => m Term -> m Term -> Term -> m Term
constructorForm' pZero pSuc v =
  case v of
    Lit (LitNat r n)
      | n == 0    -> pZero
      | n > 0     -> (`apply1` Lit (LitNat r $ n - 1)) <$> pSuc
      | otherwise -> pure v
    _ -> pure v

---------------------------------------------------------------------------
-- * The names of built-in things
---------------------------------------------------------------------------

primInteger, primIntegerPos, primIntegerNegSuc,
    primFloat, primChar, primString, primUnit, primUnitUnit, primBool, primTrue, primFalse,
    primList, primNil, primCons, primIO, primNat, primSuc, primZero,
    primPath, primPathP, primInterval, primIZero, primIOne, primPartial, primPartialP,
    primIMin, primIMax, primINeg,
    primIsOne, primItIsOne, primIsOne1, primIsOne2, primIsOneEmpty,
    primSub, primSubIn, primSubOut,
    primId, primConId, primIdElim,
    primIsEquiv, primPathToEquiv, primGlue, prim_glue, prim_unglue,
    primCompGlue, primFaceForall,
    primPushOut, primPOInl, primPOInr, primPOPush, primPOhcomp, primPOforward, primPOElim,
    primNatPlus, primNatMinus, primNatTimes, primNatDivSucAux, primNatModSucAux,
    primNatEquality, primNatLess,
    -- Machine words
    primWord64,
    primSizeUniv, primSize, primSizeLt, primSizeSuc, primSizeInf, primSizeMax,
    primInf, primSharp, primFlat,
    primEquality, primRefl,
    primRewrite, -- Name of rewrite relation
    primLevel, primLevelZero, primLevelSuc, primLevelMax,
    primSetOmega,
    primFromNat, primFromNeg, primFromString,
    -- builtins for reflection:
    primQName, primArgInfo, primArgArgInfo, primArg, primArgArg, primAbs, primAbsAbs, primAgdaTerm, primAgdaTermVar,
    primAgdaTermLam, primAgdaTermExtLam, primAgdaTermDef, primAgdaTermCon, primAgdaTermPi,
    primAgdaTermSort, primAgdaTermLit, primAgdaTermUnsupported, primAgdaTermMeta,
    primAgdaErrorPart, primAgdaErrorPartString, primAgdaErrorPartTerm, primAgdaErrorPartName,
    primHiding, primHidden, primInstance, primVisible,
    primRelevance, primRelevant, primIrrelevant,
    primAssoc, primAssocLeft, primAssocRight, primAssocNon,
    primPrecedence, primPrecRelated, primPrecUnrelated,
    primFixity, primFixityFixity,
    primAgdaLiteral, primAgdaLitNat, primAgdaLitWord64, primAgdaLitFloat, primAgdaLitString, primAgdaLitChar, primAgdaLitQName, primAgdaLitMeta,
    primAgdaSort, primAgdaSortSet, primAgdaSortLit, primAgdaSortUnsupported,
    primAgdaDefinition, primAgdaDefinitionFunDef, primAgdaDefinitionDataDef, primAgdaDefinitionRecordDef,
    primAgdaDefinitionPostulate, primAgdaDefinitionPrimitive, primAgdaDefinitionDataConstructor,
    primAgdaClause, primAgdaClauseClause, primAgdaClauseAbsurd,
    primAgdaPattern, primAgdaPatCon, primAgdaPatVar, primAgdaPatDot,
    primAgdaPatLit, primAgdaPatProj,
    primAgdaPatAbsurd,
    primAgdaMeta,
    primAgdaTCM, primAgdaTCMReturn, primAgdaTCMBind, primAgdaTCMUnify,
    primAgdaTCMTypeError, primAgdaTCMInferType, primAgdaTCMCheckType,
    primAgdaTCMNormalise, primAgdaTCMReduce,
    primAgdaTCMCatchError, primAgdaTCMGetContext, primAgdaTCMExtendContext, primAgdaTCMInContext,
    primAgdaTCMFreshName, primAgdaTCMDeclareDef, primAgdaTCMDeclarePostulate, primAgdaTCMDefineFun,
    primAgdaTCMGetType, primAgdaTCMGetDefinition,
    primAgdaTCMQuoteTerm, primAgdaTCMUnquoteTerm,
    primAgdaTCMBlockOnMeta, primAgdaTCMCommit, primAgdaTCMIsMacro,
    primAgdaTCMWithNormalisation, primAgdaTCMDebugPrint
    :: TCM Term

primInteger      = getBuiltin builtinInteger
primIntegerPos   = getBuiltin builtinIntegerPos
primIntegerNegSuc = getBuiltin builtinIntegerNegSuc
primFloat        = getBuiltin builtinFloat
primChar         = getBuiltin builtinChar
primString       = getBuiltin builtinString
primBool         = getBuiltin builtinBool
primUnit         = getBuiltin builtinUnit
primUnitUnit     = getBuiltin builtinUnitUnit
primTrue         = getBuiltin builtinTrue
primFalse        = getBuiltin builtinFalse
primList         = getBuiltin builtinList
primNil          = getBuiltin builtinNil
primCons         = getBuiltin builtinCons
primIO           = getBuiltin builtinIO
primId           = getBuiltin builtinId
primConId        = getBuiltin builtinConId
primIdElim       = getPrimitiveTerm builtinIdElim
primPath         = getBuiltin builtinPath
primPathP        = getBuiltin builtinPathP
primInterval     = getBuiltin builtinInterval
primIZero        = getBuiltin builtinIZero
primIOne         = getBuiltin builtinIOne
primIMin         = getPrimitiveTerm builtinIMin
primIMax         = getPrimitiveTerm builtinIMax
primINeg         = getPrimitiveTerm builtinINeg
primPartial      = getPrimitiveTerm "primPartial"
primPartialP     = getPrimitiveTerm "primPartialP"
primIsOne        = getBuiltin builtinIsOne
primItIsOne      = getBuiltin builtinItIsOne
primIsEquiv      = getBuiltin builtinIsEquiv
primPathToEquiv  = getBuiltin builtinPathToEquiv
primGlue         = getPrimitiveTerm builtinGlue
prim_glue        = getPrimitiveTerm builtin_glue
prim_unglue      = getPrimitiveTerm builtin_unglue
primCompGlue     = getPrimitiveTerm builtinCompGlue
primFaceForall   = getPrimitiveTerm builtinFaceForall
primIsOne1       = getBuiltin builtinIsOne1
primIsOne2       = getBuiltin builtinIsOne2
primIsOneEmpty   = getBuiltin builtinIsOneEmpty
primSub          = getBuiltin builtinSub
primSubIn        = getBuiltin builtinSubIn
primSubOut       = getPrimitiveTerm builtinSubOut
primPushOut      = getBuiltin builtinPushOut
primPOInl        = getBuiltin builtinPOInl
primPOInr        = getBuiltin builtinPOInr
primPOPush       = getBuiltin builtinPOPush
primPOhcomp      = getPrimitiveTerm builtinPOhcomp
primPOforward    = getPrimitiveTerm builtinPOforward
primPOElim       = getPrimitiveTerm builtinPOElim
primNat          = getBuiltin builtinNat
primSuc          = getBuiltin builtinSuc
primZero         = getBuiltin builtinZero
primNatPlus      = getBuiltin builtinNatPlus
primNatMinus     = getBuiltin builtinNatMinus
primNatTimes     = getBuiltin builtinNatTimes
primNatDivSucAux = getBuiltin builtinNatDivSucAux
primNatModSucAux = getBuiltin builtinNatModSucAux
primNatEquality  = getBuiltin builtinNatEquals
primNatLess      = getBuiltin builtinNatLess
primWord64       = getBuiltin builtinWord64
primSizeUniv     = getBuiltin builtinSizeUniv
primSize         = getBuiltin builtinSize
primSizeLt       = getBuiltin builtinSizeLt
primSizeSuc      = getBuiltin builtinSizeSuc
primSizeInf      = getBuiltin builtinSizeInf
primSizeMax      = getBuiltin builtinSizeMax
primInf          = getBuiltin builtinInf
primSharp        = getBuiltin builtinSharp
primFlat         = getBuiltin builtinFlat
primEquality     = getBuiltin builtinEquality
primRefl         = getBuiltin builtinRefl
primRewrite      = getBuiltin builtinRewrite
primLevel        = getBuiltin builtinLevel
primLevelZero    = getBuiltin builtinLevelZero
primLevelSuc     = getBuiltin builtinLevelSuc
primLevelMax     = getBuiltin builtinLevelMax
primSetOmega     = getBuiltin builtinSetOmega
primFromNat      = getBuiltin builtinFromNat
primFromNeg      = getBuiltin builtinFromNeg
primFromString   = getBuiltin builtinFromString
primQName        = getBuiltin builtinQName
primArg          = getBuiltin builtinArg
primArgArg       = getBuiltin builtinArgArg
primAbs          = getBuiltin builtinAbs
primAbsAbs       = getBuiltin builtinAbsAbs
primAgdaSort     = getBuiltin builtinAgdaSort
primHiding       = getBuiltin builtinHiding
primHidden       = getBuiltin builtinHidden
primInstance     = getBuiltin builtinInstance
primVisible      = getBuiltin builtinVisible
primRelevance    = getBuiltin builtinRelevance
primRelevant     = getBuiltin builtinRelevant
primIrrelevant   = getBuiltin builtinIrrelevant
primAssoc        = getBuiltin builtinAssoc
primAssocLeft    = getBuiltin builtinAssocLeft
primAssocRight   = getBuiltin builtinAssocRight
primAssocNon     = getBuiltin builtinAssocNon
primPrecedence    = getBuiltin builtinPrecedence
primPrecRelated   = getBuiltin builtinPrecRelated
primPrecUnrelated = getBuiltin builtinPrecUnrelated
primFixity        = getBuiltin builtinFixity
primFixityFixity  = getBuiltin builtinFixityFixity
primArgInfo      = getBuiltin builtinArgInfo
primArgArgInfo   = getBuiltin builtinArgArgInfo
primAgdaSortSet  = getBuiltin builtinAgdaSortSet
primAgdaSortLit  = getBuiltin builtinAgdaSortLit
primAgdaSortUnsupported = getBuiltin builtinAgdaSortUnsupported
primAgdaTerm         = getBuiltin builtinAgdaTerm
primAgdaTermVar      = getBuiltin builtinAgdaTermVar
primAgdaTermLam      = getBuiltin builtinAgdaTermLam
primAgdaTermExtLam   = getBuiltin builtinAgdaTermExtLam
primAgdaTermDef      = getBuiltin builtinAgdaTermDef
primAgdaTermCon      = getBuiltin builtinAgdaTermCon
primAgdaTermPi       = getBuiltin builtinAgdaTermPi
primAgdaTermSort     = getBuiltin builtinAgdaTermSort
primAgdaTermLit      = getBuiltin builtinAgdaTermLit
primAgdaTermUnsupported     = getBuiltin builtinAgdaTermUnsupported
primAgdaTermMeta  = getBuiltin builtinAgdaTermMeta
primAgdaErrorPart       = getBuiltin builtinAgdaErrorPart
primAgdaErrorPartString = getBuiltin builtinAgdaErrorPartString
primAgdaErrorPartTerm   = getBuiltin builtinAgdaErrorPartTerm
primAgdaErrorPartName   = getBuiltin builtinAgdaErrorPartName
primAgdaLiteral   = getBuiltin builtinAgdaLiteral
primAgdaLitNat    = getBuiltin builtinAgdaLitNat
primAgdaLitWord64 = getBuiltin builtinAgdaLitWord64
primAgdaLitFloat  = getBuiltin builtinAgdaLitFloat
primAgdaLitChar   = getBuiltin builtinAgdaLitChar
primAgdaLitString = getBuiltin builtinAgdaLitString
primAgdaLitQName  = getBuiltin builtinAgdaLitQName
primAgdaLitMeta   = getBuiltin builtinAgdaLitMeta
primAgdaPattern   = getBuiltin builtinAgdaPattern
primAgdaPatCon    = getBuiltin builtinAgdaPatCon
primAgdaPatVar    = getBuiltin builtinAgdaPatVar
primAgdaPatDot    = getBuiltin builtinAgdaPatDot
primAgdaPatLit    = getBuiltin builtinAgdaPatLit
primAgdaPatProj   = getBuiltin builtinAgdaPatProj
primAgdaPatAbsurd = getBuiltin builtinAgdaPatAbsurd
primAgdaClause    = getBuiltin builtinAgdaClause
primAgdaClauseClause = getBuiltin builtinAgdaClauseClause
primAgdaClauseAbsurd = getBuiltin builtinAgdaClauseAbsurd
primAgdaDefinitionFunDef          = getBuiltin builtinAgdaDefinitionFunDef
primAgdaDefinitionDataDef         = getBuiltin builtinAgdaDefinitionDataDef
primAgdaDefinitionRecordDef       = getBuiltin builtinAgdaDefinitionRecordDef
primAgdaDefinitionDataConstructor = getBuiltin builtinAgdaDefinitionDataConstructor
primAgdaDefinitionPostulate       = getBuiltin builtinAgdaDefinitionPostulate
primAgdaDefinitionPrimitive       = getBuiltin builtinAgdaDefinitionPrimitive
primAgdaDefinition                = getBuiltin builtinAgdaDefinition
primAgdaMeta                      = getBuiltin builtinAgdaMeta
primAgdaTCM           = getBuiltin builtinAgdaTCM
primAgdaTCMReturn     = getBuiltin builtinAgdaTCMReturn
primAgdaTCMBind       = getBuiltin builtinAgdaTCMBind
primAgdaTCMUnify      = getBuiltin builtinAgdaTCMUnify
primAgdaTCMTypeError  = getBuiltin builtinAgdaTCMTypeError
primAgdaTCMInferType  = getBuiltin builtinAgdaTCMInferType
primAgdaTCMCheckType  = getBuiltin builtinAgdaTCMCheckType
primAgdaTCMNormalise  = getBuiltin builtinAgdaTCMNormalise
primAgdaTCMReduce     = getBuiltin builtinAgdaTCMReduce
primAgdaTCMCatchError = getBuiltin builtinAgdaTCMCatchError
primAgdaTCMGetContext = getBuiltin builtinAgdaTCMGetContext
primAgdaTCMExtendContext = getBuiltin builtinAgdaTCMExtendContext
primAgdaTCMInContext     = getBuiltin builtinAgdaTCMInContext
primAgdaTCMFreshName     = getBuiltin builtinAgdaTCMFreshName
primAgdaTCMDeclareDef    = getBuiltin builtinAgdaTCMDeclareDef
primAgdaTCMDeclarePostulate   = getBuiltin builtinAgdaTCMDeclarePostulate
primAgdaTCMDefineFun     = getBuiltin builtinAgdaTCMDefineFun
primAgdaTCMGetType            = getBuiltin builtinAgdaTCMGetType
primAgdaTCMGetDefinition      = getBuiltin builtinAgdaTCMGetDefinition
primAgdaTCMQuoteTerm          = getBuiltin builtinAgdaTCMQuoteTerm
primAgdaTCMUnquoteTerm        = getBuiltin builtinAgdaTCMUnquoteTerm
primAgdaTCMBlockOnMeta        = getBuiltin builtinAgdaTCMBlockOnMeta
primAgdaTCMCommit             = getBuiltin builtinAgdaTCMCommit
primAgdaTCMIsMacro            = getBuiltin builtinAgdaTCMIsMacro
primAgdaTCMWithNormalisation  = getBuiltin builtinAgdaTCMWithNormalisation
primAgdaTCMDebugPrint         = getBuiltin builtinAgdaTCMDebugPrint

builtinNat, builtinSuc, builtinZero, builtinNatPlus, builtinNatMinus,
  builtinNatTimes, builtinNatDivSucAux, builtinNatModSucAux, builtinNatEquals,
  builtinNatLess, builtinInteger, builtinIntegerPos, builtinIntegerNegSuc,
  builtinWord64,
  builtinFloat, builtinChar, builtinString, builtinUnit, builtinUnitUnit,
  builtinBool, builtinTrue, builtinFalse,
  builtinList, builtinNil, builtinCons, builtinIO,
  builtinPath, builtinPathP, builtinInterval, builtinPathAbs, builtinIZero, builtinIOne, builtinPartial, builtinPartialP,
  builtinIMin, builtinIMax, builtinINeg,
  builtinIsOne,  builtinItIsOne, builtinIsOne1, builtinIsOne2, builtinIsOneEmpty,
  builtinSub, builtinSubIn, builtinSubOut,
  builtinIsEquiv, builtinPathToEquiv, builtinGlue, builtin_glue, builtin_unglue,
  builtinCompGlue, builtinFaceForall,
  builtinId, builtinConId, builtinIdElim,
  builtinPushOut, builtinPOInl, builtinPOInr, builtinPOPush, builtinPOhcomp, builtinPOforward, builtinPOElim,
  builtinSizeUniv, builtinSize, builtinSizeLt,
  builtinSizeSuc, builtinSizeInf, builtinSizeMax,
  builtinInf, builtinSharp, builtinFlat,
  builtinEquality, builtinRefl, builtinRewrite, builtinLevelMax,
  builtinLevel, builtinLevelZero, builtinLevelSuc,
  builtinSetOmega,
  builtinFromNat, builtinFromNeg, builtinFromString,
  builtinQName, builtinAgdaSort, builtinAgdaSortSet, builtinAgdaSortLit,
  builtinAgdaSortUnsupported,
  builtinHiding, builtinHidden, builtinInstance, builtinVisible,
  builtinRelevance, builtinRelevant, builtinIrrelevant, builtinArg,
  builtinAssoc, builtinAssocLeft, builtinAssocRight, builtinAssocNon,
  builtinPrecedence, builtinPrecRelated, builtinPrecUnrelated,
  builtinFixity, builtinFixityFixity,
  builtinArgInfo, builtinArgArgInfo, builtinArgArg,
  builtinAbs, builtinAbsAbs, builtinAgdaTerm,
  builtinAgdaTermVar, builtinAgdaTermLam, builtinAgdaTermExtLam,
  builtinAgdaTermDef, builtinAgdaTermCon, builtinAgdaTermPi,
  builtinAgdaTermSort, builtinAgdaTermLit, builtinAgdaTermUnsupported, builtinAgdaTermMeta,
  builtinAgdaErrorPart, builtinAgdaErrorPartString, builtinAgdaErrorPartTerm, builtinAgdaErrorPartName,
  builtinAgdaLiteral, builtinAgdaLitNat, builtinAgdaLitWord64, builtinAgdaLitFloat,
  builtinAgdaLitChar, builtinAgdaLitString, builtinAgdaLitQName, builtinAgdaLitMeta,
  builtinAgdaClause, builtinAgdaClauseClause, builtinAgdaClauseAbsurd, builtinAgdaPattern,
  builtinAgdaPatVar, builtinAgdaPatCon, builtinAgdaPatDot, builtinAgdaPatLit,
  builtinAgdaPatProj, builtinAgdaPatAbsurd,
  builtinAgdaDefinitionFunDef,
  builtinAgdaDefinitionDataDef, builtinAgdaDefinitionRecordDef,
  builtinAgdaDefinitionDataConstructor, builtinAgdaDefinitionPostulate,
  builtinAgdaDefinitionPrimitive, builtinAgdaDefinition,
  builtinAgdaMeta,
  builtinAgdaTCM, builtinAgdaTCMReturn, builtinAgdaTCMBind, builtinAgdaTCMUnify,
  builtinAgdaTCMTypeError, builtinAgdaTCMInferType,
  builtinAgdaTCMCheckType, builtinAgdaTCMNormalise, builtinAgdaTCMReduce,
  builtinAgdaTCMCatchError,
  builtinAgdaTCMGetContext, builtinAgdaTCMExtendContext, builtinAgdaTCMInContext,
  builtinAgdaTCMFreshName, builtinAgdaTCMDeclareDef, builtinAgdaTCMDeclarePostulate, builtinAgdaTCMDefineFun,
  builtinAgdaTCMGetType, builtinAgdaTCMGetDefinition,
  builtinAgdaTCMQuoteTerm, builtinAgdaTCMUnquoteTerm,
  builtinAgdaTCMBlockOnMeta, builtinAgdaTCMCommit, builtinAgdaTCMIsMacro,
  builtinAgdaTCMWithNormalisation, builtinAgdaTCMDebugPrint
  :: String

builtinNat                           = "NATURAL"
builtinSuc                           = "SUC"
builtinZero                          = "ZERO"
builtinNatPlus                       = "NATPLUS"
builtinNatMinus                      = "NATMINUS"
builtinNatTimes                      = "NATTIMES"
builtinNatDivSucAux                  = "NATDIVSUCAUX"
builtinNatModSucAux                  = "NATMODSUCAUX"
builtinNatEquals                     = "NATEQUALS"
builtinNatLess                       = "NATLESS"
builtinWord64                        = "WORD64"
builtinInteger                       = "INTEGER"
builtinIntegerPos                    = "INTEGERPOS"
builtinIntegerNegSuc                 = "INTEGERNEGSUC"
builtinFloat                         = "FLOAT"
builtinChar                          = "CHAR"
builtinString                        = "STRING"
builtinUnit                          = "UNIT"
builtinUnitUnit                      = "UNITUNIT"
builtinBool                          = "BOOL"
builtinTrue                          = "TRUE"
builtinFalse                         = "FALSE"
builtinList                          = "LIST"
builtinNil                           = "NIL"
builtinCons                          = "CONS"
builtinIO                            = "IO"
builtinId                            = "ID"
builtinConId                         = "CONID"
builtinIdElim                        = "primIdElim"
builtinPath                          = "PATH"
builtinPathP                         = "PATHP"
builtinInterval                      = "INTERVAL"
builtinIMin                          = "primIMin"
builtinIMax                          = "primIMax"
builtinINeg                          = "primINeg"
builtinPathAbs                       = "PATHABS"
builtinIZero                         = "IZERO"
builtinIOne                          = "IONE"
builtinPartial                       = "PARTIAL"
builtinPartialP                      = "PARTIALP"
builtinIsOne                         = "ISONE"
builtinItIsOne                       = "ITISONE"
builtinIsEquiv                       = "ISEQUIV"
builtinPathToEquiv                   = "PATHTOEQUIV"
builtinGlue                          = "primGlue"
builtin_glue                         = "prim^glue"
builtin_unglue                       = "prim^unglue"
builtinCompGlue                      = "COMPGLUE"
builtinFaceForall                    = "primFaceForall"
builtinIsOne1                        = "ISONE1"
builtinIsOne2                        = "ISONE2"
builtinIsOneEmpty                    = "ISONEEMPTY"
builtinSub                           = "SUB"
builtinSubIn                         = "SUBIN"
builtinSubOut                        = "primSubOut"
builtinPushOut                       = "PUSHOUT"
builtinPOInl                         = "PUSHOUTINL"
builtinPOInr                         = "PUSHOUTINR"
builtinPOPush                        = "PUSHOUTPUSH"
builtinPOhcomp                       = "primPushOutHComp"
builtinPOforward                     = "primPushOutForward"
builtinPOElim                        = "primPushOutElim"
builtinSizeUniv                      = "SIZEUNIV"
builtinSize                          = "SIZE"
builtinSizeLt                        = "SIZELT"
builtinSizeSuc                       = "SIZESUC"
builtinSizeInf                       = "SIZEINF"
builtinSizeMax                       = "SIZEMAX"
builtinInf                           = "INFINITY"
builtinSharp                         = "SHARP"
builtinFlat                          = "FLAT"
builtinEquality                      = "EQUALITY"
builtinRefl                          = "REFL"
builtinRewrite                       = "REWRITE"
builtinLevelMax                      = "LEVELMAX"
builtinLevel                         = "LEVEL"
builtinLevelZero                     = "LEVELZERO"
builtinLevelSuc                      = "LEVELSUC"
builtinSetOmega                      = "SETOMEGA"
builtinFromNat                       = "FROMNAT"
builtinFromNeg                       = "FROMNEG"
builtinFromString                    = "FROMSTRING"
builtinQName                         = "QNAME"
builtinAgdaSort                      = "AGDASORT"
builtinAgdaSortSet                   = "AGDASORTSET"
builtinAgdaSortLit                   = "AGDASORTLIT"
builtinAgdaSortUnsupported           = "AGDASORTUNSUPPORTED"
builtinHiding                        = "HIDING"
builtinHidden                        = "HIDDEN"
builtinInstance                      = "INSTANCE"
builtinVisible                       = "VISIBLE"
builtinRelevance                     = "RELEVANCE"
builtinRelevant                      = "RELEVANT"
builtinIrrelevant                    = "IRRELEVANT"
builtinAssoc                         = "ASSOC"
builtinAssocLeft                     = "ASSOCLEFT"
builtinAssocRight                    = "ASSOCRIGHT"
builtinAssocNon                      = "ASSOCNON"
builtinPrecedence                    = "PRECEDENCE"
builtinPrecRelated                   = "PRECRELATED"
builtinPrecUnrelated                 = "PRECUNRELATED"
builtinFixity                        = "FIXITY"
builtinFixityFixity                  = "FIXITYFIXITY"
builtinArg                           = "ARG"
builtinArgInfo                       = "ARGINFO"
builtinArgArgInfo                    = "ARGARGINFO"
builtinArgArg                        = "ARGARG"
builtinAbs                           = "ABS"
builtinAbsAbs                        = "ABSABS"
builtinAgdaTerm                      = "AGDATERM"
builtinAgdaTermVar                   = "AGDATERMVAR"
builtinAgdaTermLam                   = "AGDATERMLAM"
builtinAgdaTermExtLam                = "AGDATERMEXTLAM"
builtinAgdaTermDef                   = "AGDATERMDEF"
builtinAgdaTermCon                   = "AGDATERMCON"
builtinAgdaTermPi                    = "AGDATERMPI"
builtinAgdaTermSort                  = "AGDATERMSORT"
builtinAgdaTermLit                   = "AGDATERMLIT"
builtinAgdaTermUnsupported           = "AGDATERMUNSUPPORTED"
builtinAgdaTermMeta                  = "AGDATERMMETA"
builtinAgdaErrorPart                 = "AGDAERRORPART"
builtinAgdaErrorPartString           = "AGDAERRORPARTSTRING"
builtinAgdaErrorPartTerm             = "AGDAERRORPARTTERM"
builtinAgdaErrorPartName             = "AGDAERRORPARTNAME"
builtinAgdaLiteral                   = "AGDALITERAL"
builtinAgdaLitNat                    = "AGDALITNAT"
builtinAgdaLitWord64                 = "AGDALITWORD64"
builtinAgdaLitFloat                  = "AGDALITFLOAT"
builtinAgdaLitChar                   = "AGDALITCHAR"
builtinAgdaLitString                 = "AGDALITSTRING"
builtinAgdaLitQName                  = "AGDALITQNAME"
builtinAgdaLitMeta                   = "AGDALITMETA"
builtinAgdaClause                    = "AGDACLAUSE"
builtinAgdaClauseClause              = "AGDACLAUSECLAUSE"
builtinAgdaClauseAbsurd              = "AGDACLAUSEABSURD"
builtinAgdaPattern                   = "AGDAPATTERN"
builtinAgdaPatVar                    = "AGDAPATVAR"
builtinAgdaPatCon                    = "AGDAPATCON"
builtinAgdaPatDot                    = "AGDAPATDOT"
builtinAgdaPatLit                    = "AGDAPATLIT"
builtinAgdaPatProj                   = "AGDAPATPROJ"
builtinAgdaPatAbsurd                 = "AGDAPATABSURD"
builtinAgdaDefinitionFunDef          = "AGDADEFINITIONFUNDEF"
builtinAgdaDefinitionDataDef         = "AGDADEFINITIONDATADEF"
builtinAgdaDefinitionRecordDef       = "AGDADEFINITIONRECORDDEF"
builtinAgdaDefinitionDataConstructor = "AGDADEFINITIONDATACONSTRUCTOR"
builtinAgdaDefinitionPostulate       = "AGDADEFINITIONPOSTULATE"
builtinAgdaDefinitionPrimitive       = "AGDADEFINITIONPRIMITIVE"
builtinAgdaDefinition                = "AGDADEFINITION"
builtinAgdaMeta                      = "AGDAMETA"
builtinAgdaTCM           = "AGDATCM"
builtinAgdaTCMReturn     = "AGDATCMRETURN"
builtinAgdaTCMBind       = "AGDATCMBIND"
builtinAgdaTCMUnify      = "AGDATCMUNIFY"
builtinAgdaTCMTypeError  = "AGDATCMTYPEERROR"
builtinAgdaTCMInferType  = "AGDATCMINFERTYPE"
builtinAgdaTCMCheckType  = "AGDATCMCHECKTYPE"
builtinAgdaTCMNormalise  = "AGDATCMNORMALISE"
builtinAgdaTCMReduce     = "AGDATCMREDUCE"
builtinAgdaTCMCatchError = "AGDATCMCATCHERROR"
builtinAgdaTCMGetContext = "AGDATCMGETCONTEXT"
builtinAgdaTCMExtendContext = "AGDATCMEXTENDCONTEXT"
builtinAgdaTCMInContext     = "AGDATCMINCONTEXT"
builtinAgdaTCMFreshName     = "AGDATCMFRESHNAME"
builtinAgdaTCMDeclareDef    = "AGDATCMDECLAREDEF"
builtinAgdaTCMDeclarePostulate    = "AGDATCMDECLAREPOSTULATE"
builtinAgdaTCMDefineFun     = "AGDATCMDEFINEFUN"
builtinAgdaTCMGetType       = "AGDATCMGETTYPE"
builtinAgdaTCMGetDefinition = "AGDATCMGETDEFINITION"
builtinAgdaTCMBlockOnMeta   = "AGDATCMBLOCKONMETA"
builtinAgdaTCMCommit        = "AGDATCMCOMMIT"
builtinAgdaTCMQuoteTerm     = "AGDATCMQUOTETERM"
builtinAgdaTCMUnquoteTerm   = "AGDATCMUNQUOTETERM"
builtinAgdaTCMIsMacro       = "AGDATCMISMACRO"
builtinAgdaTCMWithNormalisation = "AGDATCMWITHNORMALISATION"
builtinAgdaTCMDebugPrint = "AGDATCMDEBUGPRINT"

-- | Builtins that come without a definition in Agda syntax.
--   These are giving names to Agda internal concepts which
--   cannot be assigned an Agda type.
--
--   An example would be a user-defined name for @Set@.
--
--     {-# BUILTIN TYPE Type #-}
--
--   The type of @Type@ would be @Type : Level → Setω@
--   which is not valid Agda.

builtinsNoDef :: [String]
builtinsNoDef =
  [ builtinSizeUniv
  , builtinSize
  , builtinSizeLt
  , builtinSizeSuc
  , builtinSizeInf
  , builtinSizeMax
  , builtinConId
  , builtinInterval
  , builtinPartial
  , builtinPartialP
  , builtinIsOne
  , builtinSub
  , builtinIZero
  , builtinIOne
  , builtinSetOmega
  , builtinString
  , builtinChar
  , builtinFloat
  , builtinWord64
  , builtinInf
  , builtinSharp
  , builtinFlat
  ]

-- | The coinductive primitives.

data CoinductionKit = CoinductionKit
  { nameOfInf   :: QName
  , nameOfSharp :: QName
  , nameOfFlat  :: QName
  }

-- | Tries to build a 'CoinductionKit'.

coinductionKit' :: TCM CoinductionKit
coinductionKit' = do
  Def inf   _ <- primInf
  Def sharp _ <- primSharp
  Def flat  _ <- primFlat
  return $ CoinductionKit
    { nameOfInf   = inf
    , nameOfSharp = sharp
    , nameOfFlat  = flat
    }

coinductionKit :: TCM (Maybe CoinductionKit)
coinductionKit = tryMaybe coinductionKit'


------------------------------------------------------------------------
-- * Path equality
------------------------------------------------------------------------

getPrimName :: Term -> QName
getPrimName ty = do
  let lamV (Lam i b)  = mapFst (getHiding i :) $ lamV (unAbs b)
      lamV (Pi _ b)   = lamV (unEl $ unAbs b)
      lamV v          = ([], v)
  case lamV ty of
            (_, Def path _) -> path
            (_, Con nm _ _)   -> conName nm
            (_, _)          -> __IMPOSSIBLE__

getBuiltinName', getPrimitiveName' :: HasBuiltins m => String -> m (Maybe QName)
getBuiltinName' n = fmap getPrimName <$> getBuiltin' n
getPrimitiveName' n = fmap primFunName <$> getPrimitive' n

isPrimitive :: HasBuiltins m => String -> QName -> m Bool
isPrimitive n q = (Just q ==) <$> getPrimitiveName' n

intervalView' :: HasBuiltins m => m (Term -> IntervalView)
intervalView' = do
  iz <- getBuiltinName' builtinIZero
  io <- getBuiltinName' builtinIOne
  imax <- getPrimitiveName' "primIMax"
  imin <- getPrimitiveName' "primIMin"
  ineg <- getPrimitiveName' "primINeg"
  return $ \ t ->
    case t of
      Def q es ->
        case es of
          [Apply x,Apply y] | Just q == imin -> IMin x y
          [Apply x,Apply y] | Just q == imax -> IMax x y
          [Apply x]         | Just q == ineg -> INeg x
          _                 -> OTerm t
      Con q _ [] | Just (conName q) == iz -> IZero
                 | Just (conName q) == io -> IOne
      _ -> OTerm t

intervalView :: HasBuiltins m => Term -> m IntervalView
intervalView t = do
  f <- intervalView'
  return (f t)

intervalUnview :: HasBuiltins m => IntervalView -> m Term
intervalUnview t = do
  f <- intervalUnview'
  return (f t)

intervalUnview' :: HasBuiltins m => m (IntervalView -> Term)
intervalUnview' = do
  iz <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIZero -- should it be a type error instead?
  io <- fromMaybe __IMPOSSIBLE__ <$> getBuiltin' builtinIOne
  imin <- (`Def` []) <$> fromMaybe __IMPOSSIBLE__ <$> getPrimitiveName' "primIMin"
  imax <- (`Def` []) <$> fromMaybe __IMPOSSIBLE__ <$> getPrimitiveName' "primIMax"
  ineg <- (`Def` []) <$> fromMaybe __IMPOSSIBLE__ <$> getPrimitiveName' "primINeg"
  return $ \ v -> case v of
             IZero -> iz
             IOne  -> io
             IMin x y -> apply imin [x,y]
             IMax x y -> apply imax [x,y]
             INeg x   -> apply ineg [x]
             OTerm t -> t

------------------------------------------------------------------------
-- * Path equality
------------------------------------------------------------------------

-- | Check whether the type is actually an path (lhs ≡ rhs)
--   and extract lhs, rhs, and their type.
--
--   Precondition: type is reduced.

pathView :: HasBuiltins m => Type -> m PathView
pathView t0 = do
  view <- pathView'
  return $ view t0

pathView' :: HasBuiltins m => m (Type -> PathView)
pathView' = do
 mpath  <- getBuiltinName' builtinPath
 mpathp <- getBuiltinName' builtinPathP
 return $ \ t0@(El s t) ->
  case t of
    Def path' [ Apply level , Apply typ , Apply lhs , Apply rhs ]
      | Just path' == mpath, Just path <- mpathp -> PathType s path level (lam_i <$> typ) lhs rhs
      where lam_i = Lam defaultArgInfo . NoAbs "_"
    Def path' [ Apply level , Apply typ , Apply lhs , Apply rhs ]
      | Just path' == mpathp, Just path <- mpathp -> PathType s path level typ lhs rhs
    _ -> OType t0

-- | Non dependent Path
idViewAsPath :: HasBuiltins m => Type -> m PathView
idViewAsPath t0@(El s t) = do
  mid <- fmap getPrimName <$> getBuiltin' builtinId
  mpath <- fmap getPrimName <$> getBuiltin' builtinPath
  case mid of
   Just path | isJust mpath -> case t of
    Def path' [ Apply level , Apply typ , Apply lhs , Apply rhs ]
      | path' == path -> return $ PathType s (fromJust mpath) level typ lhs rhs
    _ -> return $ OType t0
   _ -> return $ OType t0

boldPathView :: Type -> PathView
boldPathView t0@(El s t) = do
  case t of
    Def path' [ Apply level , Apply typ , Apply lhs , Apply rhs ]
      -> PathType s path' level typ lhs rhs
    _ -> OType t0

-- | Revert the 'PathView'.
--
--   Postcondition: type is reduced.

pathUnview :: PathView -> Type
pathUnview (OType t) = t
pathUnview (PathType s path l t lhs rhs) =
  El s $ Def path $ map Apply [l, t, lhs, rhs]

------------------------------------------------------------------------
-- * Builtin equality
------------------------------------------------------------------------

-- | Get the name of the equality type.
primEqualityName :: TCM QName
-- primEqualityName = getDef =<< primEquality  -- LEADS TO IMPORT CYCLE
primEqualityName = do
  eq <- primEquality
  -- Andreas, 2014-05-17 moved this here from TC.Rules.Def
  -- Don't know why up to 2 hidden lambdas need to be stripped,
  -- but I left the code in place.
  -- Maybe it was intended that equality could be declared
  -- in three different ways:
  -- 1. universe and type polymorphic
  -- 2. type polymorphic only
  -- 3. monomorphic.
  let lamV (Lam i b)  = mapFst (getHiding i :) $ lamV (unAbs b)
      lamV v          = ([], v)
  return $ case lamV eq of
    (_, Def equality _) -> equality
    _                   -> __IMPOSSIBLE__

-- | Check whether the type is actually an equality (lhs ≡ rhs)
--   and extract lhs, rhs, and their type.
--
--   Precondition: type is reduced.

equalityView :: Type -> TCM EqualityView
equalityView t0@(El s t) = do
  equality <- primEqualityName
  case t of
    Def equality' es | equality' == equality -> do
      let vs = fromMaybe __IMPOSSIBLE__ $ allApplyElims es
      let n = length vs
      unless (n >= 3) __IMPOSSIBLE__
      let (pars, [ typ , lhs, rhs ]) = splitAt (n-3) vs
      return $ EqualityType s equality pars typ lhs rhs
    _ -> return $ OtherType t0

-- | Revert the 'EqualityView'.
--
--   Postcondition: type is reduced.

equalityUnview :: EqualityView -> Type
equalityUnview (OtherType t) = t
equalityUnview (EqualityType s equality l t lhs rhs) =
  El s $ Def equality $ map Apply (l ++ [t, lhs, rhs])
