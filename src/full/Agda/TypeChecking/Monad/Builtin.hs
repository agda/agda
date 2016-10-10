{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Builtin where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Trans.Maybe

import qualified Data.Map as Map

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Internal as I
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Substitute

import Agda.Utils.Except ( MonadError(catchError) )
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

litType :: Literal -> TCM Type
litType l = case l of
  LitNat _ n    -> do
    _ <- primZero
    when_ (n > 0) $ primSuc
    el <$> primNat
  LitFloat _ _  -> el <$> primFloat
  LitChar _ _   -> el <$> primChar
  LitString _ _ -> el <$> primString
  LitQName _ _  -> el <$> primQName
  LitMeta _ _ _ -> el <$> primAgdaMeta
  where
    el t = El (mkType 0) t

instance MonadIO m => HasBuiltins (TCMT m) where
  getBuiltinThing b = liftM2 mplus (Map.lookup b <$> use stLocalBuiltins)
                      (Map.lookup b <$> use stImportedBuiltins)

setBuiltinThings :: BuiltinThings PrimFun -> TCM ()
setBuiltinThings b = stLocalBuiltins .= b

bindBuiltinName :: String -> Term -> TCM ()
bindBuiltinName b x = do
        builtin <- getBuiltinThing b
        case builtin of
            Just (Builtin y) -> typeError $ DuplicateBuiltinBinding b y x
            Just (Prim _)    -> typeError $ NoSuchBuiltinName b
            Nothing          -> stLocalBuiltins %= Map.insert b (Builtin x)

bindPrimitive :: String -> PrimFun -> TCM ()
bindPrimitive b pf = do
  builtin <- use stLocalBuiltins
  setBuiltinThings $ Map.insert b (Prim pf) builtin

getBuiltin :: String -> TCM Term
getBuiltin x =
  fromMaybeM (typeError $ NoBindingForBuiltin x) $ getBuiltin' x

getBuiltin' :: HasBuiltins m => String -> m (Maybe Term)
getBuiltin' x = do
    builtin <- getBuiltinThing x
    case builtin of         -- ignore sharing to make sure zero isn't reduced to Lit 0
        Just (Builtin t) -> return $ Just $ ignoreSharing $ killRange t
        _                -> return Nothing

getPrimitive' :: HasBuiltins m => String -> m (Maybe PrimFun)
getPrimitive' x = (getPrim =<<) <$> getBuiltinThing x
  where
    getPrim (Prim pf) = return pf
    getPrim _         = Nothing

getPrimitive :: String -> TCM PrimFun
getPrimitive x =
  fromMaybeM (typeError $ NoSuchPrimitiveFunction x) $ getPrimitive' x

-- | Rewrite a literal to constructor form if possible.
constructorForm :: Term -> TCM Term
constructorForm v = constructorForm' primZero primSuc v

constructorForm' :: Applicative m => m Term -> m Term -> Term -> m Term
constructorForm' pZero pSuc v =
  case ignoreSharing v of
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
    primNatPlus, primNatMinus, primNatTimes, primNatDivSucAux, primNatModSucAux,
    primNatEquality, primNatLess,
    primSizeUniv, primSize, primSizeLt, primSizeSuc, primSizeInf, primSizeMax,
    primInf, primSharp, primFlat,
    primEquality, primRefl,
    primRewrite, -- Name of rewrite relation
    primLevel, primLevelZero, primLevelSuc, primLevelMax,
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
    primAgdaLiteral, primAgdaLitNat, primAgdaLitFloat, primAgdaLitString, primAgdaLitChar, primAgdaLitQName, primAgdaLitMeta,
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
    primAgdaTCMFreshName, primAgdaTCMDeclareDef, primAgdaTCMDefineFun,
    primAgdaTCMGetType, primAgdaTCMGetDefinition,
    primAgdaTCMQuoteTerm, primAgdaTCMUnquoteTerm,
    primAgdaTCMBlockOnMeta, primAgdaTCMCommit, primAgdaTCMIsMacro
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
primAgdaTCMDefineFun     = getBuiltin builtinAgdaTCMDefineFun
primAgdaTCMGetType            = getBuiltin builtinAgdaTCMGetType
primAgdaTCMGetDefinition      = getBuiltin builtinAgdaTCMGetDefinition
primAgdaTCMQuoteTerm          = getBuiltin builtinAgdaTCMQuoteTerm
primAgdaTCMUnquoteTerm        = getBuiltin builtinAgdaTCMUnquoteTerm
primAgdaTCMBlockOnMeta        = getBuiltin builtinAgdaTCMBlockOnMeta
primAgdaTCMCommit             = getBuiltin builtinAgdaTCMCommit
primAgdaTCMIsMacro            = getBuiltin builtinAgdaTCMIsMacro

builtinNat, builtinSuc, builtinZero, builtinNatPlus, builtinNatMinus,
  builtinNatTimes, builtinNatDivSucAux, builtinNatModSucAux, builtinNatEquals,
  builtinNatLess, builtinInteger, builtinIntegerPos, builtinIntegerNegSuc,
  builtinFloat, builtinChar, builtinString, builtinUnit, builtinUnitUnit,
  builtinBool, builtinTrue, builtinFalse,
  builtinList, builtinNil, builtinCons, builtinIO,
  builtinSizeUniv, builtinSize, builtinSizeLt,
  builtinSizeSuc, builtinSizeInf, builtinSizeMax,
  builtinInf, builtinSharp, builtinFlat,
  builtinEquality, builtinRefl, builtinRewrite, builtinLevelMax,
  builtinLevel, builtinLevelZero, builtinLevelSuc,
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
  builtinAgdaLiteral, builtinAgdaLitNat, builtinAgdaLitFloat,
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
  builtinAgdaTCMFreshName, builtinAgdaTCMDeclareDef, builtinAgdaTCMDefineFun,
  builtinAgdaTCMGetType, builtinAgdaTCMGetDefinition,
  builtinAgdaTCMQuoteTerm, builtinAgdaTCMUnquoteTerm,
  builtinAgdaTCMBlockOnMeta, builtinAgdaTCMCommit, builtinAgdaTCMIsMacro
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
builtinAgdaTCMDefineFun     = "AGDATCMDEFINEFUN"
builtinAgdaTCMGetType       = "AGDATCMGETTYPE"
builtinAgdaTCMGetDefinition = "AGDATCMGETDEFINITION"
builtinAgdaTCMBlockOnMeta   = "AGDATCMBLOCKONMETA"
builtinAgdaTCMCommit        = "AGDATCMCOMMIT"
builtinAgdaTCMQuoteTerm     = "AGDATCMQUOTETERM"
builtinAgdaTCMUnquoteTerm   = "AGDATCMUNQUOTETERM"
builtinAgdaTCMIsMacro       = "AGDATCMISMACRO"

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
  Def inf   _ <- ignoreSharing <$> primInf
  Def sharp _ <- ignoreSharing <$> primSharp
  Def flat  _ <- ignoreSharing <$> primFlat
  return $ CoinductionKit
    { nameOfInf   = inf
    , nameOfSharp = sharp
    , nameOfFlat  = flat
    }

coinductionKit :: TCM (Maybe CoinductionKit)
coinductionKit = tryMaybe coinductionKit'

------------------------------------------------------------------------
-- * Builtin equality
------------------------------------------------------------------------

-- | Get the name of the equality type.
primEqualityName :: TCM QName
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
      lamV (Shared p) = lamV (derefPtr p)
      lamV v          = ([], v)
  return $ case lamV eq of
    ([Hidden, Hidden], Def equality _) -> equality
    ([Hidden],         Def equality _) -> equality
    ([],               Def equality _) -> equality
    _                                  -> __IMPOSSIBLE__

-- | Check whether the type is actually an equality (lhs ≡ rhs)
--   and extract lhs, rhs, and their type.
--
--   Precondition: type is reduced.

equalityView :: Type -> TCM EqualityView
equalityView t0@(El s t) = do
  equality <- primEqualityName
  case ignoreSharing t of
    Def equality' [ Apply level , Apply typ , Apply lhs , Apply rhs ]
      | equality' == equality -> return $ EqualityType s equality level typ lhs rhs
    _ -> return $ OtherType t0

-- | Revert the 'EqualityView'.
--
--   Postcondition: type is reduced.

equalityUnview :: EqualityView -> Type
equalityUnview (OtherType t) = t
equalityUnview (EqualityType s equality l t lhs rhs) =
  El s $ Def equality $ map Apply [l, t, lhs, rhs]
