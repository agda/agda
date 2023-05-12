-- | This module defines the names of all builtin and primitives used in Agda.
--
-- See "Agda.TypeChecking.Monad.Builtin"
module Agda.Syntax.Builtin where

import GHC.Generics (Generic)

import Control.DeepSeq (NFData)

import qualified Data.Map as M
import Data.Hashable

import Agda.Syntax.Position

import Agda.Utils.List
import Agda.Utils.Pretty

-- | Either a 'BuiltinId' or 'PrimitiveId', used for some lookups.
data SomeBuiltin
  = BuiltinName !BuiltinId
  | PrimitiveName !PrimitiveId
  deriving (Show, Eq, Ord, Generic)

instance Hashable SomeBuiltin
instance NFData SomeBuiltin

-- | The class of types which can be converted to 'SomeBuiltin'.
class IsBuiltin a where
  -- | Convert this value to a builtin.
  someBuiltin :: a -> SomeBuiltin

  -- | Get the identifier for this builtin, generally used for error messages.
  getBuiltinId :: a -> String

instance IsBuiltin SomeBuiltin where
  someBuiltin = id

  getBuiltinId (BuiltinName x) = getBuiltinId x
  getBuiltinId (PrimitiveName x) = getBuiltinId x

-- * Builtins

-- | A builtin name, defined by the @BUILTIN@ pragma.
data BuiltinId
  = BuiltinNat
  | BuiltinSuc
  | BuiltinZero
  | BuiltinNatPlus
  | BuiltinNatMinus
  | BuiltinNatTimes
  | BuiltinNatDivSucAux
  | BuiltinNatModSucAux
  | BuiltinNatEquals
  | BuiltinNatLess
  | BuiltinWord64
  | BuiltinInteger
  | BuiltinIntegerPos
  | BuiltinIntegerNegSuc
  | BuiltinFloat
  | BuiltinChar
  | BuiltinString
  | BuiltinUnit
  | BuiltinUnitUnit
  | BuiltinSigma
  | BuiltinSigmaCon
  | BuiltinBool
  | BuiltinTrue
  | BuiltinFalse
  | BuiltinList
  | BuiltinNil
  | BuiltinCons
  | BuiltinMaybe
  | BuiltinNothing
  | BuiltinJust
  | BuiltinIO
  | BuiltinId
  | BuiltinReflId
  | BuiltinPath
  | BuiltinPathP
  | BuiltinIntervalUniv
  | BuiltinInterval
  | BuiltinIZero
  | BuiltinIOne
  | BuiltinPartial
  | BuiltinPartialP
  | BuiltinIsOne
  | BuiltinItIsOne
  | BuiltinEquiv
  | BuiltinEquivFun
  | BuiltinEquivProof
  | BuiltinTranspProof
  | BuiltinIsOne1
  | BuiltinIsOne2
  | BuiltinIsOneEmpty
  | BuiltinSub
  | BuiltinSubIn
  | BuiltinSizeUniv
  | BuiltinSize
  | BuiltinSizeLt
  | BuiltinSizeSuc
  | BuiltinSizeInf
  | BuiltinSizeMax
  | BuiltinInf
  | BuiltinSharp
  | BuiltinFlat
  | BuiltinEquality
  | BuiltinRefl
  | BuiltinRewrite
  | BuiltinLevelMax
  | BuiltinLevel
  | BuiltinLevelZero
  | BuiltinLevelSuc
  | BuiltinSet
  | BuiltinProp
  | BuiltinSetOmega
  | BuiltinLevelUniv
  | BuiltinSSetOmega
  | BuiltinStrictSet
  | BuiltinFromNat
  | BuiltinFromNeg
  | BuiltinFromString
  | BuiltinQName
  | BuiltinAgdaSort
  | BuiltinAgdaSortSet
  | BuiltinAgdaSortLit
  | BuiltinAgdaSortProp
  | BuiltinAgdaSortPropLit
  | BuiltinAgdaSortInf
  | BuiltinAgdaSortUnsupported
  | BuiltinHiding
  | BuiltinHidden
  | BuiltinInstance
  | BuiltinVisible
  | BuiltinRelevance
  | BuiltinRelevant
  | BuiltinIrrelevant
  | BuiltinQuantity
  | BuiltinQuantity0
  | BuiltinQuantityω
  | BuiltinModality
  | BuiltinModalityConstructor
  | BuiltinAssoc
  | BuiltinAssocLeft
  | BuiltinAssocRight
  | BuiltinAssocNon
  | BuiltinPrecedence
  | BuiltinPrecRelated
  | BuiltinPrecUnrelated
  | BuiltinFixity
  | BuiltinFixityFixity
  | BuiltinArg
  | BuiltinArgInfo
  | BuiltinArgArgInfo
  | BuiltinArgArg
  | BuiltinAbs
  | BuiltinAbsAbs
  | BuiltinAgdaTerm
  | BuiltinAgdaTermVar
  | BuiltinAgdaTermLam
  | BuiltinAgdaTermExtLam
  | BuiltinAgdaTermDef
  | BuiltinAgdaTermCon
  | BuiltinAgdaTermPi
  | BuiltinAgdaTermSort
  | BuiltinAgdaTermLit
  | BuiltinAgdaTermUnsupported
  | BuiltinAgdaTermMeta
  | BuiltinAgdaErrorPart
  | BuiltinAgdaErrorPartString
  | BuiltinAgdaErrorPartTerm
  | BuiltinAgdaErrorPartPatt
  | BuiltinAgdaErrorPartName
  | BuiltinAgdaLiteral
  | BuiltinAgdaLitNat
  | BuiltinAgdaLitWord64
  | BuiltinAgdaLitFloat
  | BuiltinAgdaLitChar
  | BuiltinAgdaLitString
  | BuiltinAgdaLitQName
  | BuiltinAgdaLitMeta
  | BuiltinAgdaClause
  | BuiltinAgdaClauseClause
  | BuiltinAgdaClauseAbsurd
  | BuiltinAgdaPattern
  | BuiltinAgdaPatVar
  | BuiltinAgdaPatCon
  | BuiltinAgdaPatDot
  | BuiltinAgdaPatLit
  | BuiltinAgdaPatProj
  | BuiltinAgdaPatAbsurd
  | BuiltinAgdaDefinitionFunDef
  | BuiltinAgdaDefinitionDataDef
  | BuiltinAgdaDefinitionRecordDef
  | BuiltinAgdaDefinitionDataConstructor
  | BuiltinAgdaDefinitionPostulate
  | BuiltinAgdaDefinitionPrimitive
  | BuiltinAgdaDefinition
  | BuiltinAgdaMeta
  | BuiltinAgdaTCM
  | BuiltinAgdaTCMReturn
  | BuiltinAgdaTCMBind
  | BuiltinAgdaTCMUnify
  | BuiltinAgdaTCMTypeError
  | BuiltinAgdaTCMInferType
  | BuiltinAgdaTCMCheckType
  | BuiltinAgdaTCMNormalise
  | BuiltinAgdaTCMReduce
  | BuiltinAgdaTCMCatchError
  | BuiltinAgdaTCMGetContext
  | BuiltinAgdaTCMExtendContext
  | BuiltinAgdaTCMInContext
  | BuiltinAgdaTCMFreshName
  | BuiltinAgdaTCMDeclareDef
  | BuiltinAgdaTCMDeclarePostulate
  | BuiltinAgdaTCMDeclareData
  | BuiltinAgdaTCMDefineData
  | BuiltinAgdaTCMDefineFun
  | BuiltinAgdaTCMGetType
  | BuiltinAgdaTCMGetDefinition
  | BuiltinAgdaTCMBlockOnMeta
  | BuiltinAgdaTCMCommit
  | BuiltinAgdaTCMQuoteTerm
  | BuiltinAgdaTCMUnquoteTerm
  | BuiltinAgdaTCMQuoteOmegaTerm
  | BuiltinAgdaTCMIsMacro
  | BuiltinAgdaTCMWithNormalisation
  | BuiltinAgdaTCMWithReconstructed
  | BuiltinAgdaTCMWithExpandLast
  | BuiltinAgdaTCMWithReduceDefs
  | BuiltinAgdaTCMAskNormalisation
  | BuiltinAgdaTCMAskReconstructed
  | BuiltinAgdaTCMAskExpandLast
  | BuiltinAgdaTCMAskReduceDefs
  | BuiltinAgdaTCMFormatErrorParts
  | BuiltinAgdaTCMDebugPrint
  | BuiltinAgdaTCMNoConstraints
  | BuiltinAgdaTCMRunSpeculative
  | BuiltinAgdaTCMExec
  | BuiltinAgdaTCMGetInstances
  | BuiltinAgdaTCMPragmaForeign
  | BuiltinAgdaTCMPragmaCompile
  deriving (Show, Eq, Ord, Bounded, Enum, Generic)

instance NFData BuiltinId

instance Hashable BuiltinId where
  s `hashWithSalt` b = s `hashWithSalt` fromEnum b

instance KillRange BuiltinId where
  killRange = id

instance Pretty BuiltinId where
  pretty = text . getBuiltinId

instance IsBuiltin BuiltinId where
  someBuiltin = BuiltinName

  getBuiltinId BuiltinNat                               = "NATURAL"
  getBuiltinId BuiltinSuc                               = "SUC"
  getBuiltinId BuiltinZero                              = "ZERO"
  getBuiltinId BuiltinNatPlus                           = "NATPLUS"
  getBuiltinId BuiltinNatMinus                          = "NATMINUS"
  getBuiltinId BuiltinNatTimes                          = "NATTIMES"
  getBuiltinId BuiltinNatDivSucAux                      = "NATDIVSUCAUX"
  getBuiltinId BuiltinNatModSucAux                      = "NATMODSUCAUX"
  getBuiltinId BuiltinNatEquals                         = "NATEQUALS"
  getBuiltinId BuiltinNatLess                           = "NATLESS"
  getBuiltinId BuiltinWord64                            = "WORD64"
  getBuiltinId BuiltinInteger                           = "INTEGER"
  getBuiltinId BuiltinIntegerPos                        = "INTEGERPOS"
  getBuiltinId BuiltinIntegerNegSuc                     = "INTEGERNEGSUC"
  getBuiltinId BuiltinFloat                             = "FLOAT"
  getBuiltinId BuiltinChar                              = "CHAR"
  getBuiltinId BuiltinString                            = "STRING"
  getBuiltinId BuiltinUnit                              = "UNIT"
  getBuiltinId BuiltinUnitUnit                          = "UNITUNIT"
  getBuiltinId BuiltinSigma                             = "SIGMA"
  getBuiltinId BuiltinSigmaCon                          = "SIGMACON"
  getBuiltinId BuiltinBool                              = "BOOL"
  getBuiltinId BuiltinTrue                              = "TRUE"
  getBuiltinId BuiltinFalse                             = "FALSE"
  getBuiltinId BuiltinList                              = "LIST"
  getBuiltinId BuiltinNil                               = "NIL"
  getBuiltinId BuiltinCons                              = "CONS"
  getBuiltinId BuiltinMaybe                             = "MAYBE"
  getBuiltinId BuiltinNothing                           = "NOTHING"
  getBuiltinId BuiltinJust                              = "JUST"
  getBuiltinId BuiltinIO                                = "IO"
  getBuiltinId BuiltinId                                = "ID"
  getBuiltinId BuiltinReflId                            = "REFLID"
  getBuiltinId BuiltinPath                              = "PATH"
  getBuiltinId BuiltinPathP                             = "PATHP"
  getBuiltinId BuiltinIntervalUniv                      = "CUBEINTERVALUNIV"
  getBuiltinId BuiltinInterval                          = "INTERVAL"
  getBuiltinId BuiltinIZero                             = "IZERO"
  getBuiltinId BuiltinIOne                              = "IONE"
  getBuiltinId BuiltinPartial                           = "PARTIAL"
  getBuiltinId BuiltinPartialP                          = "PARTIALP"
  getBuiltinId BuiltinIsOne                             = "ISONE"
  getBuiltinId BuiltinItIsOne                           = "ITISONE"
  getBuiltinId BuiltinEquiv                             = "EQUIV"
  getBuiltinId BuiltinEquivFun                          = "EQUIVFUN"
  getBuiltinId BuiltinEquivProof                        = "EQUIVPROOF"
  getBuiltinId BuiltinTranspProof                       = "TRANSPPROOF"
  getBuiltinId BuiltinIsOne1                            = "ISONE1"
  getBuiltinId BuiltinIsOne2                            = "ISONE2"
  getBuiltinId BuiltinIsOneEmpty                        = "ISONEEMPTY"
  getBuiltinId BuiltinSub                               = "SUB"
  getBuiltinId BuiltinSubIn                             = "SUBIN"
  getBuiltinId BuiltinSizeUniv                          = "SIZEUNIV"
  getBuiltinId BuiltinSize                              = "SIZE"
  getBuiltinId BuiltinSizeLt                            = "SIZELT"
  getBuiltinId BuiltinSizeSuc                           = "SIZESUC"
  getBuiltinId BuiltinSizeInf                           = "SIZEINF"
  getBuiltinId BuiltinSizeMax                           = "SIZEMAX"
  getBuiltinId BuiltinInf                               = "INFINITY"
  getBuiltinId BuiltinSharp                             = "SHARP"
  getBuiltinId BuiltinFlat                              = "FLAT"
  getBuiltinId BuiltinEquality                          = "EQUALITY"
  getBuiltinId BuiltinRefl                              = "REFL"
  getBuiltinId BuiltinRewrite                           = "REWRITE"
  getBuiltinId BuiltinLevelMax                          = "LEVELMAX"
  getBuiltinId BuiltinLevel                             = "LEVEL"
  getBuiltinId BuiltinLevelZero                         = "LEVELZERO"
  getBuiltinId BuiltinLevelSuc                          = "LEVELSUC"
  getBuiltinId BuiltinSet                               = "TYPE"
  getBuiltinId BuiltinProp                              = "PROP"
  getBuiltinId BuiltinSetOmega                          = "SETOMEGA"
  getBuiltinId BuiltinLevelUniv                         = "LEVELUNIV"
  getBuiltinId BuiltinSSetOmega                         = "STRICTSETOMEGA"
  getBuiltinId BuiltinStrictSet                         = "STRICTSET"
  getBuiltinId BuiltinFromNat                           = "FROMNAT"
  getBuiltinId BuiltinFromNeg                           = "FROMNEG"
  getBuiltinId BuiltinFromString                        = "FROMSTRING"
  getBuiltinId BuiltinQName                             = "QNAME"
  getBuiltinId BuiltinAgdaSort                          = "AGDASORT"
  getBuiltinId BuiltinAgdaSortSet                       = "AGDASORTSET"
  getBuiltinId BuiltinAgdaSortLit                       = "AGDASORTLIT"
  getBuiltinId BuiltinAgdaSortProp                      = "AGDASORTPROP"
  getBuiltinId BuiltinAgdaSortPropLit                   = "AGDASORTPROPLIT"
  getBuiltinId BuiltinAgdaSortInf                       = "AGDASORTINF"
  getBuiltinId BuiltinAgdaSortUnsupported               = "AGDASORTUNSUPPORTED"
  getBuiltinId BuiltinHiding                            = "HIDING"
  getBuiltinId BuiltinHidden                            = "HIDDEN"
  getBuiltinId BuiltinInstance                          = "INSTANCE"
  getBuiltinId BuiltinVisible                           = "VISIBLE"
  getBuiltinId BuiltinRelevance                         = "RELEVANCE"
  getBuiltinId BuiltinRelevant                          = "RELEVANT"
  getBuiltinId BuiltinIrrelevant                        = "IRRELEVANT"
  getBuiltinId BuiltinQuantity                          = "QUANTITY"
  getBuiltinId BuiltinQuantity0                         = "QUANTITY-0"
  getBuiltinId BuiltinQuantityω                         = "QUANTITY-ω"
  getBuiltinId BuiltinModality                          = "MODALITY"
  getBuiltinId BuiltinModalityConstructor               = "MODALITY-CONSTRUCTOR"
  getBuiltinId BuiltinAssoc                             = "ASSOC"
  getBuiltinId BuiltinAssocLeft                         = "ASSOCLEFT"
  getBuiltinId BuiltinAssocRight                        = "ASSOCRIGHT"
  getBuiltinId BuiltinAssocNon                          = "ASSOCNON"
  getBuiltinId BuiltinPrecedence                        = "PRECEDENCE"
  getBuiltinId BuiltinPrecRelated                       = "PRECRELATED"
  getBuiltinId BuiltinPrecUnrelated                     = "PRECUNRELATED"
  getBuiltinId BuiltinFixity                            = "FIXITY"
  getBuiltinId BuiltinFixityFixity                      = "FIXITYFIXITY"
  getBuiltinId BuiltinArg                               = "ARG"
  getBuiltinId BuiltinArgInfo                           = "ARGINFO"
  getBuiltinId BuiltinArgArgInfo                        = "ARGARGINFO"
  getBuiltinId BuiltinArgArg                            = "ARGARG"
  getBuiltinId BuiltinAbs                               = "ABS"
  getBuiltinId BuiltinAbsAbs                            = "ABSABS"
  getBuiltinId BuiltinAgdaTerm                          = "AGDATERM"
  getBuiltinId BuiltinAgdaTermVar                       = "AGDATERMVAR"
  getBuiltinId BuiltinAgdaTermLam                       = "AGDATERMLAM"
  getBuiltinId BuiltinAgdaTermExtLam                    = "AGDATERMEXTLAM"
  getBuiltinId BuiltinAgdaTermDef                       = "AGDATERMDEF"
  getBuiltinId BuiltinAgdaTermCon                       = "AGDATERMCON"
  getBuiltinId BuiltinAgdaTermPi                        = "AGDATERMPI"
  getBuiltinId BuiltinAgdaTermSort                      = "AGDATERMSORT"
  getBuiltinId BuiltinAgdaTermLit                       = "AGDATERMLIT"
  getBuiltinId BuiltinAgdaTermUnsupported               = "AGDATERMUNSUPPORTED"
  getBuiltinId BuiltinAgdaTermMeta                      = "AGDATERMMETA"
  getBuiltinId BuiltinAgdaErrorPart                     = "AGDAERRORPART"
  getBuiltinId BuiltinAgdaErrorPartString               = "AGDAERRORPARTSTRING"
  getBuiltinId BuiltinAgdaErrorPartTerm                 = "AGDAERRORPARTTERM"
  getBuiltinId BuiltinAgdaErrorPartPatt                 = "AGDAERRORPARTPATT"
  getBuiltinId BuiltinAgdaErrorPartName                 = "AGDAERRORPARTNAME"
  getBuiltinId BuiltinAgdaLiteral                       = "AGDALITERAL"
  getBuiltinId BuiltinAgdaLitNat                        = "AGDALITNAT"
  getBuiltinId BuiltinAgdaLitWord64                     = "AGDALITWORD64"
  getBuiltinId BuiltinAgdaLitFloat                      = "AGDALITFLOAT"
  getBuiltinId BuiltinAgdaLitChar                       = "AGDALITCHAR"
  getBuiltinId BuiltinAgdaLitString                     = "AGDALITSTRING"
  getBuiltinId BuiltinAgdaLitQName                      = "AGDALITQNAME"
  getBuiltinId BuiltinAgdaLitMeta                       = "AGDALITMETA"
  getBuiltinId BuiltinAgdaClause                        = "AGDACLAUSE"
  getBuiltinId BuiltinAgdaClauseClause                  = "AGDACLAUSECLAUSE"
  getBuiltinId BuiltinAgdaClauseAbsurd                  = "AGDACLAUSEABSURD"
  getBuiltinId BuiltinAgdaPattern                       = "AGDAPATTERN"
  getBuiltinId BuiltinAgdaPatVar                        = "AGDAPATVAR"
  getBuiltinId BuiltinAgdaPatCon                        = "AGDAPATCON"
  getBuiltinId BuiltinAgdaPatDot                        = "AGDAPATDOT"
  getBuiltinId BuiltinAgdaPatLit                        = "AGDAPATLIT"
  getBuiltinId BuiltinAgdaPatProj                       = "AGDAPATPROJ"
  getBuiltinId BuiltinAgdaPatAbsurd                     = "AGDAPATABSURD"
  getBuiltinId BuiltinAgdaDefinitionFunDef              = "AGDADEFINITIONFUNDEF"
  getBuiltinId BuiltinAgdaDefinitionDataDef             = "AGDADEFINITIONDATADEF"
  getBuiltinId BuiltinAgdaDefinitionRecordDef           = "AGDADEFINITIONRECORDDEF"
  getBuiltinId BuiltinAgdaDefinitionDataConstructor     = "AGDADEFINITIONDATACONSTRUCTOR"
  getBuiltinId BuiltinAgdaDefinitionPostulate           = "AGDADEFINITIONPOSTULATE"
  getBuiltinId BuiltinAgdaDefinitionPrimitive           = "AGDADEFINITIONPRIMITIVE"
  getBuiltinId BuiltinAgdaDefinition                    = "AGDADEFINITION"
  getBuiltinId BuiltinAgdaMeta                          = "AGDAMETA"
  getBuiltinId BuiltinAgdaTCM                           = "AGDATCM"
  getBuiltinId BuiltinAgdaTCMReturn                     = "AGDATCMRETURN"
  getBuiltinId BuiltinAgdaTCMBind                       = "AGDATCMBIND"
  getBuiltinId BuiltinAgdaTCMUnify                      = "AGDATCMUNIFY"
  getBuiltinId BuiltinAgdaTCMTypeError                  = "AGDATCMTYPEERROR"
  getBuiltinId BuiltinAgdaTCMInferType                  = "AGDATCMINFERTYPE"
  getBuiltinId BuiltinAgdaTCMCheckType                  = "AGDATCMCHECKTYPE"
  getBuiltinId BuiltinAgdaTCMNormalise                  = "AGDATCMNORMALISE"
  getBuiltinId BuiltinAgdaTCMReduce                     = "AGDATCMREDUCE"
  getBuiltinId BuiltinAgdaTCMCatchError                 = "AGDATCMCATCHERROR"
  getBuiltinId BuiltinAgdaTCMGetContext                 = "AGDATCMGETCONTEXT"
  getBuiltinId BuiltinAgdaTCMExtendContext              = "AGDATCMEXTENDCONTEXT"
  getBuiltinId BuiltinAgdaTCMInContext                  = "AGDATCMINCONTEXT"
  getBuiltinId BuiltinAgdaTCMFreshName                  = "AGDATCMFRESHNAME"
  getBuiltinId BuiltinAgdaTCMDeclareDef                 = "AGDATCMDECLAREDEF"
  getBuiltinId BuiltinAgdaTCMDeclarePostulate           = "AGDATCMDECLAREPOSTULATE"
  getBuiltinId BuiltinAgdaTCMDeclareData                = "AGDATCMDECLAREDATA"
  getBuiltinId BuiltinAgdaTCMDefineData                 = "AGDATCMDEFINEDATA"
  getBuiltinId BuiltinAgdaTCMDefineFun                  = "AGDATCMDEFINEFUN"
  getBuiltinId BuiltinAgdaTCMGetType                    = "AGDATCMGETTYPE"
  getBuiltinId BuiltinAgdaTCMGetDefinition              = "AGDATCMGETDEFINITION"
  getBuiltinId BuiltinAgdaTCMBlockOnMeta                = "AGDATCMBLOCKONMETA"
  getBuiltinId BuiltinAgdaTCMCommit                     = "AGDATCMCOMMIT"
  getBuiltinId BuiltinAgdaTCMQuoteTerm                  = "AGDATCMQUOTETERM"
  getBuiltinId BuiltinAgdaTCMUnquoteTerm                = "AGDATCMUNQUOTETERM"
  getBuiltinId BuiltinAgdaTCMQuoteOmegaTerm             = "AGDATCMQUOTEOMEGATERM"
  getBuiltinId BuiltinAgdaTCMIsMacro                    = "AGDATCMISMACRO"
  getBuiltinId BuiltinAgdaTCMWithNormalisation          = "AGDATCMWITHNORMALISATION"
  getBuiltinId BuiltinAgdaTCMWithReconstructed          = "AGDATCMWITHRECONSTRUCTED"
  getBuiltinId BuiltinAgdaTCMWithExpandLast             = "AGDATCMWITHEXPANDLAST"
  getBuiltinId BuiltinAgdaTCMWithReduceDefs             = "AGDATCMWITHREDUCEDEFS"
  getBuiltinId BuiltinAgdaTCMAskNormalisation           = "AGDATCMASKNORMALISATION"
  getBuiltinId BuiltinAgdaTCMAskReconstructed           = "AGDATCMASKRECONSTRUCTED"
  getBuiltinId BuiltinAgdaTCMAskExpandLast              = "AGDATCMASKEXPANDLAST"
  getBuiltinId BuiltinAgdaTCMAskReduceDefs              = "AGDATCMASKREDUCEDEFS"
  getBuiltinId BuiltinAgdaTCMFormatErrorParts           = "AGDATCMFORMATERRORPARTS"
  getBuiltinId BuiltinAgdaTCMDebugPrint                 = "AGDATCMDEBUGPRINT"
  getBuiltinId BuiltinAgdaTCMNoConstraints              = "AGDATCMNOCONSTRAINTS"
  getBuiltinId BuiltinAgdaTCMRunSpeculative             = "AGDATCMRUNSPECULATIVE"
  getBuiltinId BuiltinAgdaTCMExec                       = "AGDATCMEXEC"
  getBuiltinId BuiltinAgdaTCMGetInstances               = "AGDATCMGETINSTANCES"
  getBuiltinId BuiltinAgdaTCMPragmaForeign              = "AGDATCMPRAGMAFOREIGN"
  getBuiltinId BuiltinAgdaTCMPragmaCompile              = "AGDATCMPRAGMACOMPILE"


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
isBuiltinNoDef :: BuiltinId -> Bool
isBuiltinNoDef = hasElem builtinsNoDef

builtinsNoDef :: [BuiltinId]
builtinsNoDef =
  sizeBuiltins ++
   -- builtinConId,
  [ builtinIntervalUniv
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
  , builtinLevelUniv
  , builtinSetOmega
  , builtinStrictSet
  , builtinSSetOmega
  ]

sizeBuiltins :: [BuiltinId]
sizeBuiltins =
  [ builtinSizeUniv
  , builtinSize
  , builtinSizeLt
  , builtinSizeSuc
  , builtinSizeInf
  , builtinSizeMax
  ]

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
  builtinIsOne,  builtinItIsOne, builtinIsOne1, builtinIsOne2, builtinIsOneEmpty,
  builtinSub, builtinSubIn,
  builtinEquiv, builtinEquivFun, builtinEquivProof,
  builtinTranspProof,
  builtinId, builtinReflId,
  builtinSizeUniv, builtinSize, builtinSizeLt,
  builtinSizeSuc, builtinSizeInf, builtinSizeMax,
  builtinInf, builtinSharp, builtinFlat,
  builtinEquality, builtinRefl, builtinRewrite, builtinLevelMax,
  builtinLevel, builtinLevelZero, builtinLevelSuc,
  builtinSet, builtinProp, builtinSetOmega, builtinStrictSet, builtinSSetOmega,
  builtinLevelUniv,
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
  builtinAgdaTCMWithNormalisation, builtinAgdaTCMWithReconstructed,
  builtinAgdaTCMWithExpandLast, builtinAgdaTCMWithReduceDefs,
  builtinAgdaTCMAskNormalisation, builtinAgdaTCMAskReconstructed,
  builtinAgdaTCMAskExpandLast, builtinAgdaTCMAskReduceDefs,
  builtinAgdaTCMNoConstraints,
  builtinAgdaTCMRunSpeculative,
  builtinAgdaTCMExec,
  builtinAgdaTCMGetInstances,
  builtinAgdaTCMPragmaForeign,
  builtinAgdaTCMPragmaCompile
  :: BuiltinId

builtinNat                               = BuiltinNat
builtinSuc                               = BuiltinSuc
builtinZero                              = BuiltinZero
builtinNatPlus                           = BuiltinNatPlus
builtinNatMinus                          = BuiltinNatMinus
builtinNatTimes                          = BuiltinNatTimes
builtinNatDivSucAux                      = BuiltinNatDivSucAux
builtinNatModSucAux                      = BuiltinNatModSucAux
builtinNatEquals                         = BuiltinNatEquals
builtinNatLess                           = BuiltinNatLess
builtinWord64                            = BuiltinWord64
builtinInteger                           = BuiltinInteger
builtinIntegerPos                        = BuiltinIntegerPos
builtinIntegerNegSuc                     = BuiltinIntegerNegSuc
builtinFloat                             = BuiltinFloat
builtinChar                              = BuiltinChar
builtinString                            = BuiltinString
builtinUnit                              = BuiltinUnit
builtinUnitUnit                          = BuiltinUnitUnit
builtinSigma                             = BuiltinSigma
builtinBool                              = BuiltinBool
builtinTrue                              = BuiltinTrue
builtinFalse                             = BuiltinFalse
builtinList                              = BuiltinList
builtinNil                               = BuiltinNil
builtinCons                              = BuiltinCons
builtinMaybe                             = BuiltinMaybe
builtinNothing                           = BuiltinNothing
builtinJust                              = BuiltinJust
builtinIO                                = BuiltinIO
builtinId                                = BuiltinId
builtinReflId                            = BuiltinReflId
builtinPath                              = BuiltinPath
builtinPathP                             = BuiltinPathP
builtinIntervalUniv                      = BuiltinIntervalUniv
builtinInterval                          = BuiltinInterval
builtinIZero                             = BuiltinIZero
builtinIOne                              = BuiltinIOne
builtinPartial                           = BuiltinPartial
builtinPartialP                          = BuiltinPartialP
builtinIsOne                             = BuiltinIsOne
builtinItIsOne                           = BuiltinItIsOne
builtinEquiv                             = BuiltinEquiv
builtinEquivFun                          = BuiltinEquivFun
builtinEquivProof                        = BuiltinEquivProof
builtinTranspProof                       = BuiltinTranspProof
builtinIsOne1                            = BuiltinIsOne1
builtinIsOne2                            = BuiltinIsOne2
builtinIsOneEmpty                        = BuiltinIsOneEmpty
builtinSub                               = BuiltinSub
builtinSubIn                             = BuiltinSubIn
builtinSizeUniv                          = BuiltinSizeUniv
builtinSize                              = BuiltinSize
builtinSizeLt                            = BuiltinSizeLt
builtinSizeSuc                           = BuiltinSizeSuc
builtinSizeInf                           = BuiltinSizeInf
builtinSizeMax                           = BuiltinSizeMax
builtinInf                               = BuiltinInf
builtinSharp                             = BuiltinSharp
builtinFlat                              = BuiltinFlat
builtinEquality                          = BuiltinEquality
builtinRefl                              = BuiltinRefl
builtinRewrite                           = BuiltinRewrite
builtinLevelMax                          = BuiltinLevelMax
builtinLevel                             = BuiltinLevel
builtinLevelZero                         = BuiltinLevelZero
builtinLevelSuc                          = BuiltinLevelSuc
builtinSet                               = BuiltinSet
builtinProp                              = BuiltinProp
builtinSetOmega                          = BuiltinSetOmega
builtinLevelUniv                         = BuiltinLevelUniv
builtinSSetOmega                         = BuiltinSSetOmega
builtinStrictSet                         = BuiltinStrictSet
builtinFromNat                           = BuiltinFromNat
builtinFromNeg                           = BuiltinFromNeg
builtinFromString                        = BuiltinFromString
builtinQName                             = BuiltinQName
builtinAgdaSort                          = BuiltinAgdaSort
builtinAgdaSortSet                       = BuiltinAgdaSortSet
builtinAgdaSortLit                       = BuiltinAgdaSortLit
builtinAgdaSortProp                      = BuiltinAgdaSortProp
builtinAgdaSortPropLit                   = BuiltinAgdaSortPropLit
builtinAgdaSortInf                       = BuiltinAgdaSortInf
builtinAgdaSortUnsupported               = BuiltinAgdaSortUnsupported
builtinHiding                            = BuiltinHiding
builtinHidden                            = BuiltinHidden
builtinInstance                          = BuiltinInstance
builtinVisible                           = BuiltinVisible
builtinRelevance                         = BuiltinRelevance
builtinRelevant                          = BuiltinRelevant
builtinIrrelevant                        = BuiltinIrrelevant
builtinQuantity                          = BuiltinQuantity
builtinQuantity0                         = BuiltinQuantity0
builtinQuantityω                         = BuiltinQuantityω
builtinModality                          = BuiltinModality
builtinModalityConstructor               = BuiltinModalityConstructor
builtinAssoc                             = BuiltinAssoc
builtinAssocLeft                         = BuiltinAssocLeft
builtinAssocRight                        = BuiltinAssocRight
builtinAssocNon                          = BuiltinAssocNon
builtinPrecedence                        = BuiltinPrecedence
builtinPrecRelated                       = BuiltinPrecRelated
builtinPrecUnrelated                     = BuiltinPrecUnrelated
builtinFixity                            = BuiltinFixity
builtinFixityFixity                      = BuiltinFixityFixity
builtinArg                               = BuiltinArg
builtinArgInfo                           = BuiltinArgInfo
builtinArgArgInfo                        = BuiltinArgArgInfo
builtinArgArg                            = BuiltinArgArg
builtinAbs                               = BuiltinAbs
builtinAbsAbs                            = BuiltinAbsAbs
builtinAgdaTerm                          = BuiltinAgdaTerm
builtinAgdaTermVar                       = BuiltinAgdaTermVar
builtinAgdaTermLam                       = BuiltinAgdaTermLam
builtinAgdaTermExtLam                    = BuiltinAgdaTermExtLam
builtinAgdaTermDef                       = BuiltinAgdaTermDef
builtinAgdaTermCon                       = BuiltinAgdaTermCon
builtinAgdaTermPi                        = BuiltinAgdaTermPi
builtinAgdaTermSort                      = BuiltinAgdaTermSort
builtinAgdaTermLit                       = BuiltinAgdaTermLit
builtinAgdaTermUnsupported               = BuiltinAgdaTermUnsupported
builtinAgdaTermMeta                      = BuiltinAgdaTermMeta
builtinAgdaErrorPart                     = BuiltinAgdaErrorPart
builtinAgdaErrorPartString               = BuiltinAgdaErrorPartString
builtinAgdaErrorPartTerm                 = BuiltinAgdaErrorPartTerm
builtinAgdaErrorPartPatt                 = BuiltinAgdaErrorPartPatt
builtinAgdaErrorPartName                 = BuiltinAgdaErrorPartName
builtinAgdaLiteral                       = BuiltinAgdaLiteral
builtinAgdaLitNat                        = BuiltinAgdaLitNat
builtinAgdaLitWord64                     = BuiltinAgdaLitWord64
builtinAgdaLitFloat                      = BuiltinAgdaLitFloat
builtinAgdaLitChar                       = BuiltinAgdaLitChar
builtinAgdaLitString                     = BuiltinAgdaLitString
builtinAgdaLitQName                      = BuiltinAgdaLitQName
builtinAgdaLitMeta                       = BuiltinAgdaLitMeta
builtinAgdaClause                        = BuiltinAgdaClause
builtinAgdaClauseClause                  = BuiltinAgdaClauseClause
builtinAgdaClauseAbsurd                  = BuiltinAgdaClauseAbsurd
builtinAgdaPattern                       = BuiltinAgdaPattern
builtinAgdaPatVar                        = BuiltinAgdaPatVar
builtinAgdaPatCon                        = BuiltinAgdaPatCon
builtinAgdaPatDot                        = BuiltinAgdaPatDot
builtinAgdaPatLit                        = BuiltinAgdaPatLit
builtinAgdaPatProj                       = BuiltinAgdaPatProj
builtinAgdaPatAbsurd                     = BuiltinAgdaPatAbsurd
builtinAgdaDefinitionFunDef              = BuiltinAgdaDefinitionFunDef
builtinAgdaDefinitionDataDef             = BuiltinAgdaDefinitionDataDef
builtinAgdaDefinitionRecordDef           = BuiltinAgdaDefinitionRecordDef
builtinAgdaDefinitionDataConstructor     = BuiltinAgdaDefinitionDataConstructor
builtinAgdaDefinitionPostulate           = BuiltinAgdaDefinitionPostulate
builtinAgdaDefinitionPrimitive           = BuiltinAgdaDefinitionPrimitive
builtinAgdaDefinition                    = BuiltinAgdaDefinition
builtinAgdaMeta                          = BuiltinAgdaMeta
builtinAgdaTCM                           = BuiltinAgdaTCM
builtinAgdaTCMReturn                     = BuiltinAgdaTCMReturn
builtinAgdaTCMBind                       = BuiltinAgdaTCMBind
builtinAgdaTCMUnify                      = BuiltinAgdaTCMUnify
builtinAgdaTCMTypeError                  = BuiltinAgdaTCMTypeError
builtinAgdaTCMInferType                  = BuiltinAgdaTCMInferType
builtinAgdaTCMCheckType                  = BuiltinAgdaTCMCheckType
builtinAgdaTCMNormalise                  = BuiltinAgdaTCMNormalise
builtinAgdaTCMReduce                     = BuiltinAgdaTCMReduce
builtinAgdaTCMCatchError                 = BuiltinAgdaTCMCatchError
builtinAgdaTCMGetContext                 = BuiltinAgdaTCMGetContext
builtinAgdaTCMExtendContext              = BuiltinAgdaTCMExtendContext
builtinAgdaTCMInContext                  = BuiltinAgdaTCMInContext
builtinAgdaTCMFreshName                  = BuiltinAgdaTCMFreshName
builtinAgdaTCMDeclareDef                 = BuiltinAgdaTCMDeclareDef
builtinAgdaTCMDeclarePostulate           = BuiltinAgdaTCMDeclarePostulate
builtinAgdaTCMDeclareData                = BuiltinAgdaTCMDeclareData
builtinAgdaTCMDefineData                 = BuiltinAgdaTCMDefineData
builtinAgdaTCMDefineFun                  = BuiltinAgdaTCMDefineFun
builtinAgdaTCMGetType                    = BuiltinAgdaTCMGetType
builtinAgdaTCMGetDefinition              = BuiltinAgdaTCMGetDefinition
builtinAgdaTCMBlockOnMeta                = BuiltinAgdaTCMBlockOnMeta
builtinAgdaTCMCommit                     = BuiltinAgdaTCMCommit
builtinAgdaTCMQuoteTerm                  = BuiltinAgdaTCMQuoteTerm
builtinAgdaTCMUnquoteTerm                = BuiltinAgdaTCMUnquoteTerm
builtinAgdaTCMQuoteOmegaTerm             = BuiltinAgdaTCMQuoteOmegaTerm
builtinAgdaTCMIsMacro                    = BuiltinAgdaTCMIsMacro
builtinAgdaTCMWithNormalisation          = BuiltinAgdaTCMWithNormalisation
builtinAgdaTCMWithReconstructed          = BuiltinAgdaTCMWithReconstructed
builtinAgdaTCMWithExpandLast             = BuiltinAgdaTCMWithExpandLast
builtinAgdaTCMWithReduceDefs             = BuiltinAgdaTCMWithReduceDefs
builtinAgdaTCMAskNormalisation           = BuiltinAgdaTCMAskNormalisation
builtinAgdaTCMAskReconstructed           = BuiltinAgdaTCMAskReconstructed
builtinAgdaTCMAskExpandLast              = BuiltinAgdaTCMAskExpandLast
builtinAgdaTCMAskReduceDefs              = BuiltinAgdaTCMAskReduceDefs
builtinAgdaTCMFormatErrorParts           = BuiltinAgdaTCMFormatErrorParts
builtinAgdaTCMDebugPrint                 = BuiltinAgdaTCMDebugPrint
builtinAgdaTCMNoConstraints              = BuiltinAgdaTCMNoConstraints
builtinAgdaTCMRunSpeculative             = BuiltinAgdaTCMRunSpeculative
builtinAgdaTCMExec                       = BuiltinAgdaTCMExec
builtinAgdaTCMGetInstances               = BuiltinAgdaTCMGetInstances
builtinAgdaTCMPragmaForeign              = BuiltinAgdaTCMPragmaForeign
builtinAgdaTCMPragmaCompile              = BuiltinAgdaTCMPragmaCompile

-- | Lookup a builtin by the string used in the @BUILTIN@ pragma.
builtinById :: String -> Maybe BuiltinId
builtinById = flip M.lookup m where
  m = M.fromList [(getBuiltinId x, x) | x <- [(minBound :: BuiltinId)..]]

-- * Primitives

-- | A primitive name, defined by the @primitive@ block.
data PrimitiveId
  -- Cubical
  = PrimConId
  | PrimIdElim
  | PrimIMin
  | PrimIMax
  | PrimINeg
  | PrimPartial
  | PrimPartialP
  | PrimSubOut
  | PrimGlue
  | Prim_glue
  | Prim_unglue
  | Prim_glueU
  | Prim_unglueU
  | PrimFaceForall
  | PrimComp
  | PrimPOr
  | PrimTrans
  | PrimDepIMin
  | PrimIdFace
  | PrimIdPath
  | PrimHComp
  --  Integer
  | PrimShowInteger
  -- Natural
  | PrimNatPlus
  | PrimNatMinus
  | PrimNatTimes
  | PrimNatDivSucAux
  | PrimNatModSucAux
  | PrimNatEquality
  | PrimNatLess
  | PrimShowNat
  -- Word64
  | PrimWord64FromNat
  | PrimWord64ToNat
  | PrimWord64ToNatInjective
  -- Level
  | PrimLevelZero
  | PrimLevelSuc
  | PrimLevelMax
  -- Float
  | PrimFloatEquality
  | PrimFloatInequality
  | PrimFloatLess
  | PrimFloatIsInfinite
  | PrimFloatIsNaN
  | PrimFloatIsNegativeZero
  | PrimFloatIsSafeInteger
  | PrimFloatToWord64
  | PrimFloatToWord64Injective
  | PrimNatToFloat
  | PrimIntToFloat
  | PrimFloatRound
  | PrimFloatFloor
  | PrimFloatCeiling
  | PrimFloatToRatio
  | PrimRatioToFloat
  | PrimFloatDecode
  | PrimFloatEncode
  | PrimShowFloat
  | PrimFloatPlus
  | PrimFloatMinus
  | PrimFloatTimes
  | PrimFloatNegate
  | PrimFloatDiv
  | PrimFloatPow
  | PrimFloatSqrt
  | PrimFloatExp
  | PrimFloatLog
  | PrimFloatSin
  | PrimFloatCos
  | PrimFloatTan
  | PrimFloatASin
  | PrimFloatACos
  | PrimFloatATan
  | PrimFloatATan2
  | PrimFloatSinh
  | PrimFloatCosh
  | PrimFloatTanh
  | PrimFloatASinh
  | PrimFloatACosh
  | PrimFloatATanh
  -- Character
  | PrimCharEquality
  | PrimIsLower
  | PrimIsDigit
  | PrimIsAlpha
  | PrimIsSpace
  | PrimIsAscii
  | PrimIsLatin1
  | PrimIsPrint
  | PrimIsHexDigit
  | PrimToUpper
  | PrimToLower
  | PrimCharToNat
  | PrimCharToNatInjective
  | PrimNatToChar
  | PrimShowChar
  -- String
  | PrimStringToList
  | PrimStringToListInjective
  | PrimStringFromList
  | PrimStringFromListInjective
  | PrimStringAppend
  | PrimStringEquality
  | PrimShowString
  | PrimStringUncons
  -- "Other stuff"
  | PrimErase
  | PrimEraseEquality
  | PrimForce
  | PrimForceLemma
  | PrimQNameEquality
  | PrimQNameLess
  | PrimShowQName
  | PrimQNameFixity
  | PrimQNameToWord64s
  | PrimQNameToWord64sInjective
  | PrimMetaEquality
  | PrimMetaLess
  | PrimShowMeta
  | PrimMetaToNat
  | PrimMetaToNatInjective
  | PrimLockUniv
  deriving (Show, Eq, Ord, Bounded, Enum, Generic)

instance NFData PrimitiveId

instance Hashable PrimitiveId where
  s `hashWithSalt` b = s `hashWithSalt` fromEnum b

instance KillRange PrimitiveId where
  killRange = id

instance Pretty PrimitiveId where
  pretty = text . getBuiltinId

instance IsBuiltin PrimitiveId where
  someBuiltin = PrimitiveName

  -- Cubical
  getBuiltinId PrimConId                             = "primConId"
  getBuiltinId PrimIdElim                            = "primIdElim"
  getBuiltinId PrimIMin                              = "primIMin"
  getBuiltinId PrimIMax                              = "primIMax"
  getBuiltinId PrimINeg                              = "primINeg"
  getBuiltinId PrimPartial                           = "primPartial"
  getBuiltinId PrimPartialP                          = "primPartialP"
  getBuiltinId PrimSubOut                            = "primSubOut"
  getBuiltinId PrimGlue                              = "primGlue"
  getBuiltinId Prim_glue                             = "prim^glue"
  getBuiltinId Prim_unglue                           = "prim^unglue"
  getBuiltinId Prim_glueU                            = "prim^glueU"
  getBuiltinId Prim_unglueU                          = "prim^unglueU"
  getBuiltinId PrimFaceForall                        = "primFaceForall"
  getBuiltinId PrimComp                              = "primComp"
  getBuiltinId PrimPOr                               = "primPOr"
  getBuiltinId PrimTrans                             = "primTransp"
  getBuiltinId PrimDepIMin                           = "primDepIMin"
  getBuiltinId PrimIdFace                            = "primIdFace"
  getBuiltinId PrimIdPath                            = "primIdPath"
  getBuiltinId PrimHComp                             = "primHComp"
  --  Integer
  getBuiltinId PrimShowInteger                       = "primShowInteger"
  -- Natural
  getBuiltinId PrimNatPlus                           = "primNatPlus"
  getBuiltinId PrimNatMinus                          = "primNatMinus"
  getBuiltinId PrimNatTimes                          = "primNatTimes"
  getBuiltinId PrimNatDivSucAux                      = "primNatDivSucAux"
  getBuiltinId PrimNatModSucAux                      = "primNatModSucAux"
  getBuiltinId PrimNatEquality                       = "primNatEquality"
  getBuiltinId PrimNatLess                           = "primNatLess"
  getBuiltinId PrimShowNat                           = "primShowNat"
  -- Word64
  getBuiltinId PrimWord64FromNat                     = "primWord64FromNat"
  getBuiltinId PrimWord64ToNat                       = "primWord64ToNat"
  getBuiltinId PrimWord64ToNatInjective              = "primWord64ToNatInjective"
  -- Level
  getBuiltinId PrimLevelZero                         = "primLevelZero"
  getBuiltinId PrimLevelSuc                          = "primLevelSuc"
  getBuiltinId PrimLevelMax                          = "primLevelMax"
  -- Float
  getBuiltinId PrimFloatEquality                     = "primFloatEquality"
  getBuiltinId PrimFloatInequality                   = "primFloatInequality"
  getBuiltinId PrimFloatLess                         = "primFloatLess"
  getBuiltinId PrimFloatIsInfinite                   = "primFloatIsInfinite"
  getBuiltinId PrimFloatIsNaN                        = "primFloatIsNaN"
  getBuiltinId PrimFloatIsNegativeZero               = "primFloatIsNegativeZero"
  getBuiltinId PrimFloatIsSafeInteger                = "primFloatIsSafeInteger"
  getBuiltinId PrimFloatToWord64                     = "primFloatToWord64"
  getBuiltinId PrimFloatToWord64Injective            = "primFloatToWord64Injective"
  getBuiltinId PrimNatToFloat                        = "primNatToFloat"
  getBuiltinId PrimIntToFloat                        = "primIntToFloat"
  getBuiltinId PrimFloatRound                        = "primFloatRound"
  getBuiltinId PrimFloatFloor                        = "primFloatFloor"
  getBuiltinId PrimFloatCeiling                      = "primFloatCeiling"
  getBuiltinId PrimFloatToRatio                      = "primFloatToRatio"
  getBuiltinId PrimRatioToFloat                      = "primRatioToFloat"
  getBuiltinId PrimFloatDecode                       = "primFloatDecode"
  getBuiltinId PrimFloatEncode                       = "primFloatEncode"
  getBuiltinId PrimShowFloat                         = "primShowFloat"
  getBuiltinId PrimFloatPlus                         = "primFloatPlus"
  getBuiltinId PrimFloatMinus                        = "primFloatMinus"
  getBuiltinId PrimFloatTimes                        = "primFloatTimes"
  getBuiltinId PrimFloatNegate                       = "primFloatNegate"
  getBuiltinId PrimFloatDiv                          = "primFloatDiv"
  getBuiltinId PrimFloatPow                          = "primFloatPow"
  getBuiltinId PrimFloatSqrt                         = "primFloatSqrt"
  getBuiltinId PrimFloatExp                          = "primFloatExp"
  getBuiltinId PrimFloatLog                          = "primFloatLog"
  getBuiltinId PrimFloatSin                          = "primFloatSin"
  getBuiltinId PrimFloatCos                          = "primFloatCos"
  getBuiltinId PrimFloatTan                          = "primFloatTan"
  getBuiltinId PrimFloatASin                         = "primFloatASin"
  getBuiltinId PrimFloatACos                         = "primFloatACos"
  getBuiltinId PrimFloatATan                         = "primFloatATan"
  getBuiltinId PrimFloatATan2                        = "primFloatATan2"
  getBuiltinId PrimFloatSinh                         = "primFloatSinh"
  getBuiltinId PrimFloatCosh                         = "primFloatCosh"
  getBuiltinId PrimFloatTanh                         = "primFloatTanh"
  getBuiltinId PrimFloatASinh                        = "primFloatASinh"
  getBuiltinId PrimFloatACosh                        = "primFloatACosh"
  getBuiltinId PrimFloatATanh                        = "primFloatATanh"
  -- Character
  getBuiltinId PrimCharEquality                      = "primCharEquality"
  getBuiltinId PrimIsLower                           = "primIsLower"
  getBuiltinId PrimIsDigit                           = "primIsDigit"
  getBuiltinId PrimIsAlpha                           = "primIsAlpha"
  getBuiltinId PrimIsSpace                           = "primIsSpace"
  getBuiltinId PrimIsAscii                           = "primIsAscii"
  getBuiltinId PrimIsLatin1                          = "primIsLatin1"
  getBuiltinId PrimIsPrint                           = "primIsPrint"
  getBuiltinId PrimIsHexDigit                        = "primIsHexDigit"
  getBuiltinId PrimToUpper                           = "primToUpper"
  getBuiltinId PrimToLower                           = "primToLower"
  getBuiltinId PrimCharToNat                         = "primCharToNat"
  getBuiltinId PrimCharToNatInjective                = "primCharToNatInjective"
  getBuiltinId PrimNatToChar                         = "primNatToChar"
  getBuiltinId PrimShowChar                          = "primShowChar"
  -- String
  getBuiltinId PrimStringToList                      = "primStringToList"
  getBuiltinId PrimStringToListInjective             = "primStringToListInjective"
  getBuiltinId PrimStringFromList                    = "primStringFromList"
  getBuiltinId PrimStringFromListInjective           = "primStringFromListInjective"
  getBuiltinId PrimStringAppend                      = "primStringAppend"
  getBuiltinId PrimStringEquality                    = "primStringEquality"
  getBuiltinId PrimShowString                        = "primShowString"
  getBuiltinId PrimStringUncons                      = "primStringUncons"
  -- "Other stuff"
  getBuiltinId PrimErase                             = "primErase"
  getBuiltinId PrimEraseEquality                     = "primEraseEquality"
  getBuiltinId PrimForce                             = "primForce"
  getBuiltinId PrimForceLemma                        = "primForceLemma"
  getBuiltinId PrimQNameEquality                     = "primQNameEquality"
  getBuiltinId PrimQNameLess                         = "primQNameLess"
  getBuiltinId PrimShowQName                         = "primShowQName"
  getBuiltinId PrimQNameFixity                       = "primQNameFixity"
  getBuiltinId PrimQNameToWord64s                    = "primQNameToWord64s"
  getBuiltinId PrimQNameToWord64sInjective           = "primQNameToWord64sInjective"
  getBuiltinId PrimMetaEquality                      = "primMetaEquality"
  getBuiltinId PrimMetaLess                          = "primMetaLess"
  getBuiltinId PrimShowMeta                          = "primShowMeta"
  getBuiltinId PrimMetaToNat                         = "primMetaToNat"
  getBuiltinId PrimMetaToNatInjective                = "primMetaToNatInjective"
  getBuiltinId PrimLockUniv                          = "primLockUniv"

builtinConId, builtinIdElim, builtinSubOut,
  builtinIMin, builtinIMax, builtinINeg,
  builtinGlue, builtin_glue, builtin_unglue, builtin_glueU, builtin_unglueU,
  builtinFaceForall, builtinComp, builtinPOr,
  builtinTrans,  builtinDepIMin,
  builtinIdFace, builtinIdPath, builtinHComp, builtinLockUniv
  :: PrimitiveId
builtinConId                             = PrimConId
builtinIdElim                            = PrimIdElim
builtinIMin                              = PrimIMin
builtinIMax                              = PrimIMax
builtinINeg                              = PrimINeg
builtinSubOut                            = PrimSubOut
builtinGlue                              = PrimGlue
builtin_glue                             = Prim_glue
builtin_unglue                           = Prim_unglue
builtin_glueU                            = Prim_glueU
builtin_unglueU                          = Prim_unglueU
builtinFaceForall                        = PrimFaceForall
builtinComp                              = PrimComp
builtinPOr                               = PrimPOr
builtinTrans                             = PrimTrans
builtinDepIMin                           = PrimDepIMin
builtinIdFace                            = PrimIdFace
builtinIdPath                            = PrimIdPath
builtinHComp                             = PrimHComp
builtinLockUniv                          = PrimLockUniv

-- | Lookup a primitive by its identifier.
primitiveById :: String -> Maybe PrimitiveId
primitiveById = flip M.lookup m where
  m = M.fromList [(getBuiltinId x, x) | x <- [(minBound :: PrimitiveId)..]]
