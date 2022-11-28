-- | This module defines the names of all BUILTINs.
module Agda.Syntax.Builtin where

import Agda.Utils.List

builtinNat, builtinSuc, builtinZero, builtinNatPlus, builtinNatMinus,
  builtinNatTimes, builtinNatDivSucAux, builtinNatModSucAux, builtinNatEquals,
  builtinNatLess, builtinInteger, builtinIntegerPos, builtinIntegerNegSuc,
  builtinWord64,
  builtinFloat, builtinChar, builtinString, builtinUnit, builtinUnitUnit,
  builtinSigma,
  builtinBool, builtinTrue, builtinFalse,
  builtinList, builtinNil, builtinCons, builtinIO,
  builtinMaybe, builtinNothing, builtinJust,
  builtinPath, builtinPathP, builtinInterval, builtinIZero, builtinIOne, builtinPartial, builtinPartialP,
  builtinIMin, builtinIMax, builtinINeg,
  builtinIsOne,  builtinItIsOne, builtinIsOne1, builtinIsOne2, builtinIsOneEmpty,
  builtinComp, builtinPOr,
  builtinTrans, builtinHComp,
  builtinSub, builtinSubIn, builtinSubOut,
  builtinEquiv, builtinEquivFun, builtinEquivProof,
  builtinTranspProof,
  builtinGlue, builtin_glue, builtin_unglue,
  builtin_glueU, builtin_unglueU,
  builtinFaceForall,
  builtinId, builtinReflId, builtinConId, builtinIdElim,
  builtinSizeUniv, builtinSize, builtinSizeLt,
  builtinSizeSuc, builtinSizeInf, builtinSizeMax,
  builtinInf, builtinSharp, builtinFlat,
  builtinEquality, builtinRefl, builtinRewrite, builtinLevelMax,
  builtinLevel, builtinLevelZero, builtinLevelSuc,
  builtinSet, builtinProp, builtinSetOmega, builtinStrictSet, builtinSSetOmega,
  builtinLockUniv,
  builtinIntervalUniv,
  builtinFromNat, builtinFromNeg, builtinFromString,
  builtinQName, builtinAgdaSort, builtinAgdaSortSet, builtinAgdaSortLit,
  builtinAgdaSortProp, builtinAgdaSortPropLit, builtinAgdaSortInf,
  builtinAgdaSortUnsupported,
  builtinHiding, builtinHidden, builtinInstance, builtinVisible,
  builtinRelevance, builtinRelevant, builtinIrrelevant,
  builtinQuantity, builtinQuantity0, builtinQuantityω,
  builtinModality, builtinModalityConstructor,
  builtinAssoc, builtinAssocLeft, builtinAssocRight, builtinAssocNon,
  builtinPrecedence, builtinPrecRelated, builtinPrecUnrelated,
  builtinFixity, builtinFixityFixity,
  builtinArgInfo, builtinArgArgInfo,
  builtinArg, builtinArgArg,
  builtinAbs, builtinAbsAbs, builtinAgdaTerm,
  builtinAgdaTermVar, builtinAgdaTermLam, builtinAgdaTermExtLam,
  builtinAgdaTermDef, builtinAgdaTermCon, builtinAgdaTermPi,
  builtinAgdaTermSort, builtinAgdaTermLit, builtinAgdaTermUnsupported, builtinAgdaTermMeta,
  builtinAgdaErrorPart, builtinAgdaErrorPartString, builtinAgdaErrorPartTerm, builtinAgdaErrorPartPatt, builtinAgdaErrorPartName,
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
  builtinAgdaTCMFreshName, builtinAgdaTCMDeclareDef, builtinAgdaTCMDeclarePostulate, builtinAgdaTCMDeclareData, builtinAgdaTCMDefineData, builtinAgdaTCMDefineFun,
  builtinAgdaTCMGetType, builtinAgdaTCMGetDefinition,
  builtinAgdaTCMQuoteTerm, builtinAgdaTCMUnquoteTerm, builtinAgdaTCMQuoteOmegaTerm,
  builtinAgdaTCMBlockOnMeta, builtinAgdaTCMCommit, builtinAgdaTCMIsMacro,
  builtinAgdaTCMFormatErrorParts, builtinAgdaTCMDebugPrint,
  builtinAgdaTCMWithNormalisation, builtinAgdaTCMWithReconsParams,
  builtinAgdaTCMOnlyReduceDefs, builtinAgdaTCMDontReduceDefs,
  builtinAgdaTCMNoConstraints,
  builtinAgdaTCMRunSpeculative,
  builtinAgdaTCMExec,
  builtinAgdaTCMGetInstances,
  builtinAgdaTCMPragmaForeign,
  builtinAgdaTCMPragmaCompile
  :: String

builtinNat                               = "NATURAL"
builtinSuc                               = "SUC"
builtinZero                              = "ZERO"
builtinNatPlus                           = "NATPLUS"
builtinNatMinus                          = "NATMINUS"
builtinNatTimes                          = "NATTIMES"
builtinNatDivSucAux                      = "NATDIVSUCAUX"
builtinNatModSucAux                      = "NATMODSUCAUX"
builtinNatEquals                         = "NATEQUALS"
builtinNatLess                           = "NATLESS"
builtinWord64                            = "WORD64"
builtinInteger                           = "INTEGER"
builtinIntegerPos                        = "INTEGERPOS"
builtinIntegerNegSuc                     = "INTEGERNEGSUC"
builtinFloat                             = "FLOAT"
builtinChar                              = "CHAR"
builtinString                            = "STRING"
builtinUnit                              = "UNIT"
builtinUnitUnit                          = "UNITUNIT"
builtinSigma                             = "SIGMA"
builtinBool                              = "BOOL"
builtinTrue                              = "TRUE"
builtinFalse                             = "FALSE"
builtinList                              = "LIST"
builtinNil                               = "NIL"
builtinCons                              = "CONS"
builtinMaybe                             = "MAYBE"
builtinNothing                           = "NOTHING"
builtinJust                              = "JUST"
builtinIO                                = "IO"
builtinId                                = "ID"
builtinReflId                            = "REFLID"
builtinConId                             = "primConId"
builtinIdElim                            = "primIdElim"
builtinPath                              = "PATH"
builtinPathP                             = "PATHP"
builtinIntervalUniv                      = "CUBEINTERVALUNIV"
builtinInterval                          = "INTERVAL"
builtinIMin                              = "primIMin"
builtinIMax                              = "primIMax"
builtinINeg                              = "primINeg"
builtinIZero                             = "IZERO"
builtinIOne                              = "IONE"
builtinPartial                           = "PARTIAL"
builtinPartialP                          = "PARTIALP"
builtinIsOne                             = "ISONE"
builtinItIsOne                           = "ITISONE"
builtinEquiv                             = "EQUIV"
builtinEquivFun                          = "EQUIVFUN"
builtinEquivProof                        = "EQUIVPROOF"
builtinTranspProof                       = "TRANSPPROOF"
builtinGlue                              = "primGlue"
builtin_glue                             = "prim^glue"
builtin_unglue                           = "prim^unglue"
builtin_glueU                            = "prim^glueU"
builtin_unglueU                          = "prim^unglueU"
builtinFaceForall                        = "primFaceForall"
builtinIsOne1                            = "ISONE1"
builtinIsOne2                            = "ISONE2"
builtinIsOneEmpty                        = "ISONEEMPTY"
builtinComp                              = "primComp"
builtinPOr                               = "primPOr"
builtinTrans                             = "primTransp"
builtinHComp                             = "primHComp"
builtinSub                               = "SUB"
builtinSubIn                             = "SUBIN"
builtinSubOut                            = "primSubOut"
builtinSizeUniv                          = "SIZEUNIV"
builtinSize                              = "SIZE"
builtinSizeLt                            = "SIZELT"
builtinSizeSuc                           = "SIZESUC"
builtinSizeInf                           = "SIZEINF"
builtinSizeMax                           = "SIZEMAX"
builtinInf                               = "INFINITY"
builtinSharp                             = "SHARP"
builtinFlat                              = "FLAT"
builtinEquality                          = "EQUALITY"
builtinRefl                              = "REFL"
builtinRewrite                           = "REWRITE"
builtinLevelMax                          = "LEVELMAX"
builtinLevel                             = "LEVEL"
builtinLevelZero                         = "LEVELZERO"
builtinLevelSuc                          = "LEVELSUC"
builtinSet                               = "TYPE"
builtinProp                              = "PROP"
builtinSetOmega                          = "SETOMEGA"
builtinLockUniv                          = "primLockUniv"
builtinSSetOmega                         = "STRICTSETOMEGA"
builtinStrictSet                         = "STRICTSET"
builtinFromNat                           = "FROMNAT"
builtinFromNeg                           = "FROMNEG"
builtinFromString                        = "FROMSTRING"
builtinQName                             = "QNAME"
builtinAgdaSort                          = "AGDASORT"
builtinAgdaSortSet                       = "AGDASORTSET"
builtinAgdaSortLit                       = "AGDASORTLIT"
builtinAgdaSortProp                      = "AGDASORTPROP"
builtinAgdaSortPropLit                   = "AGDASORTPROPLIT"
builtinAgdaSortInf                       = "AGDASORTINF"
builtinAgdaSortUnsupported               = "AGDASORTUNSUPPORTED"
builtinHiding                            = "HIDING"
builtinHidden                            = "HIDDEN"
builtinInstance                          = "INSTANCE"
builtinVisible                           = "VISIBLE"
builtinRelevance                         = "RELEVANCE"
builtinRelevant                          = "RELEVANT"
builtinIrrelevant                        = "IRRELEVANT"
builtinQuantity                          = "QUANTITY"
builtinQuantity0                         = "QUANTITY-0"
builtinQuantityω                         = "QUANTITY-ω"
builtinModality                          = "MODALITY"
builtinModalityConstructor               = "MODALITY-CONSTRUCTOR"
builtinAssoc                             = "ASSOC"
builtinAssocLeft                         = "ASSOCLEFT"
builtinAssocRight                        = "ASSOCRIGHT"
builtinAssocNon                          = "ASSOCNON"
builtinPrecedence                        = "PRECEDENCE"
builtinPrecRelated                       = "PRECRELATED"
builtinPrecUnrelated                     = "PRECUNRELATED"
builtinFixity                            = "FIXITY"
builtinFixityFixity                      = "FIXITYFIXITY"
builtinArg                               = "ARG"
builtinArgInfo                           = "ARGINFO"
builtinArgArgInfo                        = "ARGARGINFO"
builtinArgArg                            = "ARGARG"
builtinAbs                               = "ABS"
builtinAbsAbs                            = "ABSABS"
builtinAgdaTerm                          = "AGDATERM"
builtinAgdaTermVar                       = "AGDATERMVAR"
builtinAgdaTermLam                       = "AGDATERMLAM"
builtinAgdaTermExtLam                    = "AGDATERMEXTLAM"
builtinAgdaTermDef                       = "AGDATERMDEF"
builtinAgdaTermCon                       = "AGDATERMCON"
builtinAgdaTermPi                        = "AGDATERMPI"
builtinAgdaTermSort                      = "AGDATERMSORT"
builtinAgdaTermLit                       = "AGDATERMLIT"
builtinAgdaTermUnsupported               = "AGDATERMUNSUPPORTED"
builtinAgdaTermMeta                      = "AGDATERMMETA"
builtinAgdaErrorPart                     = "AGDAERRORPART"
builtinAgdaErrorPartString               = "AGDAERRORPARTSTRING"
builtinAgdaErrorPartTerm                 = "AGDAERRORPARTTERM"
builtinAgdaErrorPartPatt                 = "AGDAERRORPARTPATT"
builtinAgdaErrorPartName                 = "AGDAERRORPARTNAME"
builtinAgdaLiteral                       = "AGDALITERAL"
builtinAgdaLitNat                        = "AGDALITNAT"
builtinAgdaLitWord64                     = "AGDALITWORD64"
builtinAgdaLitFloat                      = "AGDALITFLOAT"
builtinAgdaLitChar                       = "AGDALITCHAR"
builtinAgdaLitString                     = "AGDALITSTRING"
builtinAgdaLitQName                      = "AGDALITQNAME"
builtinAgdaLitMeta                       = "AGDALITMETA"
builtinAgdaClause                        = "AGDACLAUSE"
builtinAgdaClauseClause                  = "AGDACLAUSECLAUSE"
builtinAgdaClauseAbsurd                  = "AGDACLAUSEABSURD"
builtinAgdaPattern                       = "AGDAPATTERN"
builtinAgdaPatVar                        = "AGDAPATVAR"
builtinAgdaPatCon                        = "AGDAPATCON"
builtinAgdaPatDot                        = "AGDAPATDOT"
builtinAgdaPatLit                        = "AGDAPATLIT"
builtinAgdaPatProj                       = "AGDAPATPROJ"
builtinAgdaPatAbsurd                     = "AGDAPATABSURD"
builtinAgdaDefinitionFunDef              = "AGDADEFINITIONFUNDEF"
builtinAgdaDefinitionDataDef             = "AGDADEFINITIONDATADEF"
builtinAgdaDefinitionRecordDef           = "AGDADEFINITIONRECORDDEF"
builtinAgdaDefinitionDataConstructor     = "AGDADEFINITIONDATACONSTRUCTOR"
builtinAgdaDefinitionPostulate           = "AGDADEFINITIONPOSTULATE"
builtinAgdaDefinitionPrimitive           = "AGDADEFINITIONPRIMITIVE"
builtinAgdaDefinition                    = "AGDADEFINITION"
builtinAgdaMeta                          = "AGDAMETA"
builtinAgdaTCM                           = "AGDATCM"
builtinAgdaTCMReturn                     = "AGDATCMRETURN"
builtinAgdaTCMBind                       = "AGDATCMBIND"
builtinAgdaTCMUnify                      = "AGDATCMUNIFY"
builtinAgdaTCMTypeError                  = "AGDATCMTYPEERROR"
builtinAgdaTCMInferType                  = "AGDATCMINFERTYPE"
builtinAgdaTCMCheckType                  = "AGDATCMCHECKTYPE"
builtinAgdaTCMNormalise                  = "AGDATCMNORMALISE"
builtinAgdaTCMReduce                     = "AGDATCMREDUCE"
builtinAgdaTCMCatchError                 = "AGDATCMCATCHERROR"
builtinAgdaTCMGetContext                 = "AGDATCMGETCONTEXT"
builtinAgdaTCMExtendContext              = "AGDATCMEXTENDCONTEXT"
builtinAgdaTCMInContext                  = "AGDATCMINCONTEXT"
builtinAgdaTCMFreshName                  = "AGDATCMFRESHNAME"
builtinAgdaTCMDeclareDef                 = "AGDATCMDECLAREDEF"
builtinAgdaTCMDeclarePostulate           = "AGDATCMDECLAREPOSTULATE"
builtinAgdaTCMDeclareData                = "AGDATCMDECLAREDATA"
builtinAgdaTCMDefineData                 = "AGDATCMDEFINEDATA"
builtinAgdaTCMDefineFun                  = "AGDATCMDEFINEFUN"
builtinAgdaTCMGetType                    = "AGDATCMGETTYPE"
builtinAgdaTCMGetDefinition              = "AGDATCMGETDEFINITION"
builtinAgdaTCMBlockOnMeta                = "AGDATCMBLOCKONMETA"
builtinAgdaTCMCommit                     = "AGDATCMCOMMIT"
builtinAgdaTCMQuoteTerm                  = "AGDATCMQUOTETERM"
builtinAgdaTCMUnquoteTerm                = "AGDATCMUNQUOTETERM"
builtinAgdaTCMQuoteOmegaTerm             = "AGDATCMQUOTEOMEGATERM"
builtinAgdaTCMIsMacro                    = "AGDATCMISMACRO"
builtinAgdaTCMWithNormalisation          = "AGDATCMWITHNORMALISATION"
builtinAgdaTCMWithReconsParams           = "AGDATCMWITHRECONSPARAMS"
builtinAgdaTCMFormatErrorParts           = "AGDATCMFORMATERRORPARTS"
builtinAgdaTCMDebugPrint                 = "AGDATCMDEBUGPRINT"
builtinAgdaTCMOnlyReduceDefs             = "AGDATCMONLYREDUCEDEFS"
builtinAgdaTCMDontReduceDefs             = "AGDATCMDONTREDUCEDEFS"
builtinAgdaTCMNoConstraints              = "AGDATCMNOCONSTRAINTS"
builtinAgdaTCMRunSpeculative             = "AGDATCMRUNSPECULATIVE"
builtinAgdaTCMExec                       = "AGDATCMEXEC"
builtinAgdaTCMGetInstances               = "AGDATCMGETINSTANCES"
builtinAgdaTCMPragmaForeign              = "AGDATCMPRAGMAFOREIGN"
builtinAgdaTCMPragmaCompile              = "AGDATCMPRAGMACOMPILE"

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

isBuiltinNoDef :: String -> Bool
isBuiltinNoDef = hasElem builtinsNoDef

builtinsNoDef :: [String]
builtinsNoDef =
  sizeBuiltins ++
  [ builtinConId
  , builtinIntervalUniv
  , builtinId
  , builtinReflId
  , builtinInterval
  , builtinPartial
  , builtinPartialP
  , builtinIsOne
  , builtinSub
  , builtinIZero
  , builtinIOne
  , builtinSet
  , builtinProp
  , builtinSetOmega
  , builtinStrictSet
  , builtinSSetOmega
  ]

sizeBuiltins :: [String]
sizeBuiltins =
  [ builtinSizeUniv
  , builtinSize
  , builtinSizeLt
  , builtinSizeSuc
  , builtinSizeInf
  , builtinSizeMax
  ]
