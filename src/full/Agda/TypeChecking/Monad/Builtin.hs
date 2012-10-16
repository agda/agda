
module Agda.TypeChecking.Monad.Builtin where

import Control.Monad.Error
import Control.Monad.State

import Data.Functor
import qualified Data.Map as Map

import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

import Agda.Utils.Monad (when_)

litType :: Literal -> TCM Type
litType l = case l of
    LitInt _ n	  -> do
      primZero
      when_ (n > 0) $ primSuc
      el <$> primNat
    LitFloat _ _  -> el <$> primFloat
    LitChar _ _   -> el <$> primChar
    LitString _ _ -> el <$> primString
    LitQName _ _  -> el <$> primQName
  where
    el t = El (mkType 0) t

getBuiltinThing :: String -> TCM (Maybe (Builtin PrimFun))
getBuiltinThing b = liftM2 mplus (Map.lookup b <$> gets stLocalBuiltins)
                    (Map.lookup b <$> gets stImportedBuiltins)

setBuiltinThings :: BuiltinThings PrimFun -> TCM ()
setBuiltinThings b = modify $ \s -> s { stLocalBuiltins = b }

bindBuiltinName :: String -> Term -> TCM ()
bindBuiltinName b x = do
	builtin <- getBuiltinThing b
	case builtin of
	    Just (Builtin y) -> typeError $ DuplicateBuiltinBinding b y x
	    Just (Prim _)    -> typeError $ NoSuchBuiltinName b
	    Nothing	     -> modify $ \st ->
              st { stLocalBuiltins =
                    Map.insert b (Builtin x) $ stLocalBuiltins st
                 }

bindPrimitive :: String -> PrimFun -> TCM ()
bindPrimitive b pf = do
  builtin <- gets stLocalBuiltins
  setBuiltinThings $ Map.insert b (Prim pf) builtin


getBuiltin :: String -> TCM Term
getBuiltin x = do
    mt <- getBuiltin' x
    case mt of
        Nothing -> typeError $ NoBindingForBuiltin x
        Just t  -> return t

getBuiltin' :: String -> TCM (Maybe Term)
getBuiltin' x = do
    builtin <- getBuiltinThing x
    case builtin of
	Just (Builtin t) -> return $ Just (killRange t)
	_		 -> return Nothing

getPrimitive :: String -> TCM PrimFun
getPrimitive x = do
    builtin <- getBuiltinThing x
    case builtin of
	Just (Prim pf) -> return pf
	_	       -> typeError $ NoSuchPrimitiveFunction x

---------------------------------------------------------------------------
-- * The names of built-in things
---------------------------------------------------------------------------

primInteger, primFloat, primChar, primString, primBool, primTrue, primFalse,
    primList, primNil, primCons, primIO, primNat, primSuc, primZero,
    primNatPlus, primNatMinus, primNatTimes, primNatDivSucAux, primNatModSucAux,
    primNatEquality, primNatLess,
    primSize, primSizeLt, primSizeSuc, primSizeInf,
    primInf, primSharp, primFlat,
    primEquality, primRefl,
    primLevel, primLevelZero, primLevelSuc, primLevelMax,
    primIrrAxiom,
    -- builtins for reflection:
    primQName, primArg, primArgArg, primAgdaTerm, primAgdaTermVar,
    primAgdaTermLam, primAgdaTermDef, primAgdaTermCon, primAgdaTermPi,
    primAgdaTermSort, primAgdaTermUnsupported,
    primAgdaType, primAgdaTypeEl,
    primHiding, primHidden, primInstance, primVisible,
    primRelevance, primRelevant, primIrrelevant,
    primAgdaSort, primAgdaSortSet, primAgdaSortLit, primAgdaSortUnsupported,
    primAgdaDefinition, primAgdaDefinitionFunDef, primAgdaDefinitionDataDef, primAgdaDefinitionRecordDef,
    primAgdaDefinitionPostulate, primAgdaDefinitionPrimitive, primAgdaDefinitionDataConstructor,
    primAgdaFunDef, primAgdaDataDef, primAgdaRecordDef
    :: TCM Term
primInteger      = getBuiltin builtinInteger
primFloat        = getBuiltin builtinFloat
primChar         = getBuiltin builtinChar
primString       = getBuiltin builtinString
primBool         = getBuiltin builtinBool
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
primLevel        = getBuiltin builtinLevel
primLevelZero    = getBuiltin builtinLevelZero
primLevelSuc     = getBuiltin builtinLevelSuc
primLevelMax     = getBuiltin builtinLevelMax
primIrrAxiom     = getBuiltin builtinIrrAxiom
primQName        = getBuiltin builtinQName
primArg          = getBuiltin builtinArg
primArgArg       = getBuiltin builtinArgArg
primAgdaSort     = getBuiltin builtinAgdaSort
primAgdaType     = getBuiltin builtinAgdaType
primAgdaTypeEl   = getBuiltin builtinAgdaTypeEl
primHiding       = getBuiltin builtinHiding
primHidden       = getBuiltin builtinHidden
primInstance     = getBuiltin builtinInstance
primVisible      = getBuiltin builtinVisible
primRelevance    = getBuiltin builtinRelevance
primRelevant     = getBuiltin builtinRelevant
primIrrelevant   = getBuiltin builtinIrrelevant
primAgdaSortSet  = getBuiltin builtinAgdaSortSet
primAgdaSortLit  = getBuiltin builtinAgdaSortLit
primAgdaSortUnsupported = getBuiltin builtinAgdaSortUnsupported
primAgdaTerm         = getBuiltin builtinAgdaTerm
primAgdaTermVar      = getBuiltin builtinAgdaTermVar
primAgdaTermLam      = getBuiltin builtinAgdaTermLam
primAgdaTermDef      = getBuiltin builtinAgdaTermDef
primAgdaTermCon      = getBuiltin builtinAgdaTermCon
primAgdaTermPi       = getBuiltin builtinAgdaTermPi
primAgdaTermSort     = getBuiltin builtinAgdaTermSort
primAgdaTermUnsupported     = getBuiltin builtinAgdaTermUnsupported
primAgdaFunDef                    = getBuiltin builtinAgdaFunDef
primAgdaDataDef                   = getBuiltin builtinAgdaDataDef
primAgdaRecordDef                 = getBuiltin builtinAgdaRecordDef
primAgdaDefinitionFunDef          = getBuiltin builtinAgdaDefinitionFunDef
primAgdaDefinitionDataDef         = getBuiltin builtinAgdaDefinitionDataDef
primAgdaDefinitionRecordDef       = getBuiltin builtinAgdaDefinitionRecordDef
primAgdaDefinitionDataConstructor = getBuiltin builtinAgdaDefinitionDataConstructor
primAgdaDefinitionPostulate       = getBuiltin builtinAgdaDefinitionPostulate
primAgdaDefinitionPrimitive       = getBuiltin builtinAgdaDefinitionPrimitive
primAgdaDefinition                = getBuiltin builtinAgdaDefinition
builtinNat          = "NATURAL"
builtinSuc          = "SUC"
builtinZero         = "ZERO"
builtinNatPlus      = "NATPLUS"
builtinNatMinus     = "NATMINUS"
builtinNatTimes     = "NATTIMES"
builtinNatDivSucAux = "NATDIVSUCAUX"
builtinNatModSucAux = "NATMODSUCAUX"
builtinNatEquals    = "NATEQUALS"
builtinNatLess      = "NATLESS"
builtinInteger      = "INTEGER"
builtinFloat        = "FLOAT"
builtinChar         = "CHAR"
builtinString       = "STRING"
builtinBool         = "BOOL"
builtinTrue         = "TRUE"
builtinFalse        = "FALSE"
builtinList         = "LIST"
builtinNil          = "NIL"
builtinCons         = "CONS"
builtinIO           = "IO"
builtinSize         = "SIZE"
builtinSizeLt       = "SIZELT"
builtinSizeSuc      = "SIZESUC"
builtinSizeInf      = "SIZEINF"
builtinSizeMax      = "SIZEMAX"
builtinInf          = "INFINITY"
builtinSharp        = "SHARP"
builtinFlat         = "FLAT"
builtinEquality     = "EQUALITY"
builtinRefl         = "REFL"
builtinLevelMax     = "LEVELMAX"
builtinLevel        = "LEVEL"
builtinLevelZero    = "LEVELZERO"
builtinLevelSuc     = "LEVELSUC"
builtinIrrAxiom     = "IRRAXIOM"
builtinQName        = "QNAME"
builtinAgdaSort     = "AGDASORT"
builtinAgdaSortSet  = "AGDASORTSET"
builtinAgdaSortLit  = "AGDASORTLIT"
builtinAgdaSortUnsupported = "AGDASORTUNSUPPORTED"
builtinAgdaType     = "AGDATYPE"
builtinAgdaTypeEl   = "AGDATYPEEL"
builtinHiding       = "HIDING"
builtinHidden       = "HIDDEN"
builtinInstance     = "INSTANCE"
builtinVisible      = "VISIBLE"
builtinRelevance    = "RELEVANCE"
builtinRelevant     = "RELEVANT"
builtinIrrelevant   = "IRRELEVANT"
builtinArg          = "ARG"
builtinArgArg       = "ARGARG"
builtinAgdaTerm         = "AGDATERM"
builtinAgdaTermVar      = "AGDATERMVAR"
builtinAgdaTermLam      = "AGDATERMLAM"
builtinAgdaTermDef      = "AGDATERMDEF"
builtinAgdaTermCon      = "AGDATERMCON"
builtinAgdaTermPi       = "AGDATERMPI"
builtinAgdaTermSort     = "AGDATERMSORT"
builtinAgdaTermUnsupported = "AGDATERMUNSUPPORTED"
builtinAgdaFunDef                    = "AGDAFUNDEF"
builtinAgdaDataDef                   = "AGDADATADEF"
builtinAgdaRecordDef                 = "AGDARECORDDEF"
builtinAgdaDefinitionFunDef          = "AGDADEFINITIONFUNDEF"
builtinAgdaDefinitionDataDef         = "AGDADEFINITIONDATADEF"
builtinAgdaDefinitionRecordDef       = "AGDADEFINITIONRECORDDEF"
builtinAgdaDefinitionDataConstructor = "AGDADEFINITIONDATACONSTRUCTOR"
builtinAgdaDefinitionPostulate       = "AGDADEFINITIONPOSTULATE"
builtinAgdaDefinitionPrimitive       = "AGDADEFINITIONPRIMITIVE"
builtinAgdaDefinition                = "AGDADEFINITION"

-- | The coinductive primitives.

data CoinductionKit = CoinductionKit
  { nameOfInf   :: QName
  , nameOfSharp :: QName
  , nameOfFlat  :: QName
  }

-- | Tries to build a 'CoinductionKit'.

coinductionKit :: TCM (Maybe CoinductionKit)
coinductionKit = (do
  Def inf   _ <- ignoreSharing <$> primInf
  Def sharp _ <- ignoreSharing <$> primSharp
  Def flat  _ <- ignoreSharing <$> primFlat
  return $ Just $ CoinductionKit
    { nameOfInf   = inf
    , nameOfSharp = sharp
    , nameOfFlat  = flat
    })
    `catchError` \_ -> return Nothing
