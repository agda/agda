
module Agda.TypeChecking.Monad.Builtin
  ( module Agda.TypeChecking.Monad.Builtin
  , module Agda.Syntax.Builtin  -- The names are defined here.
  ) where

import qualified Control.Monad.Fail as Fail

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Writer

import qualified Data.Map as Map
import Data.Function ( on )

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Builtin
import Agda.Syntax.Internal as I
import Agda.TypeChecking.Monad.Base
-- import Agda.TypeChecking.Functions  -- LEADS TO IMPORT CYCLE
import Agda.TypeChecking.Substitute

import Agda.Utils.Except
import Agda.Utils.ListT
import Agda.Utils.Monad
import Agda.Utils.Maybe
import Agda.Utils.Tuple

import Agda.Utils.Impossible

class ( Functor m
      , Applicative m
      , Fail.MonadFail m
      ) => HasBuiltins m where
  getBuiltinThing :: String -> m (Maybe (Builtin PrimFun))

instance HasBuiltins m => HasBuiltins (MaybeT m) where
  getBuiltinThing b = lift $ getBuiltinThing b

instance HasBuiltins m => HasBuiltins (ExceptT e m) where
  getBuiltinThing b = lift $ getBuiltinThing b

instance HasBuiltins m => HasBuiltins (ListT m) where
  getBuiltinThing b = lift $ getBuiltinThing b

instance HasBuiltins m => HasBuiltins (ReaderT e m) where
  getBuiltinThing b = lift $ getBuiltinThing b

instance HasBuiltins m => HasBuiltins (StateT s m) where
  getBuiltinThing b = lift $ getBuiltinThing b

instance (HasBuiltins m, Monoid w) => HasBuiltins (WriterT w m) where
  getBuiltinThing b = lift $ getBuiltinThing b

-- If Agda is changed so that the type of a literal can belong to an
-- inductive family (with at least one index), then the implementation
-- of split' in Agda.TypeChecking.Coverage should be changed.

litType
  :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m)
  => Literal -> m Type
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
  builtin <- getBuiltinThing b
  case builtin of
    Just (Builtin _) -> typeError $ NoSuchPrimitiveFunction b
    Just (Prim x)    -> typeError $ (DuplicatePrimitiveBinding b `on` primFunName) x pf
    Nothing          -> stLocalBuiltins `modifyTCLens` Map.insert b (Prim pf)

getBuiltin :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m)
           => String -> m Term
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

getPrimitive :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m)
             => String -> m PrimFun
getPrimitive x =
  fromMaybeM (typeError $ NoSuchPrimitiveFunction x) $ getPrimitive' x

getPrimitiveTerm :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m)
                 => String -> m Term
getPrimitiveTerm x = (`Def` []) <$> primFunName <$> getPrimitive x

getPrimitiveTerm' :: HasBuiltins m => String -> m (Maybe Term)
getPrimitiveTerm' x = fmap (`Def` []) <$> getPrimitiveName' x

getTerm' :: HasBuiltins m => String -> m (Maybe Term)
getTerm' x = mplus <$> getBuiltin' x <*> getPrimitiveTerm' x

getName' :: HasBuiltins m => String -> m (Maybe QName)
getName' x = mplus <$> getBuiltinName' x <*> getPrimitiveName' x

-- | @getTerm use name@ looks up @name@ as a primitive or builtin, and
-- throws an error otherwise.
-- The @use@ argument describes how the name is used for the sake of
-- the error message.
getTerm :: (HasBuiltins m) => String -> String -> m Term
getTerm use name = flip fromMaybeM (getTerm' name) $
  return $! (throwImpossible $ ImpMissingDefinitions [name] use)


-- | Rewrite a literal to constructor form if possible.
constructorForm :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m)
                => Term -> m Term
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
    primSigma,
    primList, primNil, primCons, primIO, primNat, primSuc, primZero,
    primPath, primPathP, primInterval, primIZero, primIOne, primPartial, primPartialP,
    primIMin, primIMax, primINeg,
    primIsOne, primItIsOne, primIsOne1, primIsOne2, primIsOneEmpty,
    primSub, primSubIn, primSubOut,
    primTrans, primHComp,
    primId, primConId, primIdElim,
    primEquiv, primEquivFun, primEquivProof,
    primTranspProof,
    primGlue, prim_glue, prim_unglue,
    prim_glueU, prim_unglueU,
    primFaceForall,
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
    primAgdaTCMWithNormalisation, primAgdaTCMDebugPrint,
    primAgdaTCMNoConstraints,
    primAgdaTCMRunSpeculative
    :: (HasBuiltins m, MonadError TCErr m, MonadTCEnv m, ReadTCState m) => m Term

primInteger                           = getBuiltin builtinInteger
primIntegerPos                        = getBuiltin builtinIntegerPos
primIntegerNegSuc                     = getBuiltin builtinIntegerNegSuc
primFloat                             = getBuiltin builtinFloat
primChar                              = getBuiltin builtinChar
primString                            = getBuiltin builtinString
primBool                              = getBuiltin builtinBool
primSigma                             = getBuiltin builtinSigma
primUnit                              = getBuiltin builtinUnit
primUnitUnit                          = getBuiltin builtinUnitUnit
primTrue                              = getBuiltin builtinTrue
primFalse                             = getBuiltin builtinFalse
primList                              = getBuiltin builtinList
primNil                               = getBuiltin builtinNil
primCons                              = getBuiltin builtinCons
primIO                                = getBuiltin builtinIO
primId                                = getBuiltin builtinId
primConId                             = getBuiltin builtinConId
primIdElim                            = getPrimitiveTerm builtinIdElim
primPath                              = getBuiltin builtinPath
primPathP                             = getBuiltin builtinPathP
primInterval                          = getBuiltin builtinInterval
primIZero                             = getBuiltin builtinIZero
primIOne                              = getBuiltin builtinIOne
primIMin                              = getPrimitiveTerm builtinIMin
primIMax                              = getPrimitiveTerm builtinIMax
primINeg                              = getPrimitiveTerm builtinINeg
primPartial                           = getPrimitiveTerm "primPartial"
primPartialP                          = getPrimitiveTerm "primPartialP"
primIsOne                             = getBuiltin builtinIsOne
primItIsOne                           = getBuiltin builtinItIsOne
primTrans                             = getPrimitiveTerm builtinTrans
primHComp                             = getPrimitiveTerm builtinHComp
primEquiv                             = getBuiltin builtinEquiv
primEquivFun                          = getBuiltin builtinEquivFun
primEquivProof                        = getBuiltin builtinEquivProof
primTranspProof                       = getBuiltin builtinTranspProof
prim_glueU                            = getPrimitiveTerm builtin_glueU
prim_unglueU                          = getPrimitiveTerm builtin_unglueU
primGlue                              = getPrimitiveTerm builtinGlue
prim_glue                             = getPrimitiveTerm builtin_glue
prim_unglue                           = getPrimitiveTerm builtin_unglue
primFaceForall                        = getPrimitiveTerm builtinFaceForall
primIsOne1                            = getBuiltin builtinIsOne1
primIsOne2                            = getBuiltin builtinIsOne2
primIsOneEmpty                        = getBuiltin builtinIsOneEmpty
primSub                               = getBuiltin builtinSub
primSubIn                             = getBuiltin builtinSubIn
primSubOut                            = getPrimitiveTerm builtinSubOut
primNat                               = getBuiltin builtinNat
primSuc                               = getBuiltin builtinSuc
primZero                              = getBuiltin builtinZero
primNatPlus                           = getBuiltin builtinNatPlus
primNatMinus                          = getBuiltin builtinNatMinus
primNatTimes                          = getBuiltin builtinNatTimes
primNatDivSucAux                      = getBuiltin builtinNatDivSucAux
primNatModSucAux                      = getBuiltin builtinNatModSucAux
primNatEquality                       = getBuiltin builtinNatEquals
primNatLess                           = getBuiltin builtinNatLess
primWord64                            = getBuiltin builtinWord64
primSizeUniv                          = getBuiltin builtinSizeUniv
primSize                              = getBuiltin builtinSize
primSizeLt                            = getBuiltin builtinSizeLt
primSizeSuc                           = getBuiltin builtinSizeSuc
primSizeInf                           = getBuiltin builtinSizeInf
primSizeMax                           = getBuiltin builtinSizeMax
primInf                               = getBuiltin builtinInf
primSharp                             = getBuiltin builtinSharp
primFlat                              = getBuiltin builtinFlat
primEquality                          = getBuiltin builtinEquality
primRefl                              = getBuiltin builtinRefl
primRewrite                           = getBuiltin builtinRewrite
primLevel                             = getBuiltin builtinLevel
primLevelZero                         = getBuiltin builtinLevelZero
primLevelSuc                          = getBuiltin builtinLevelSuc
primLevelMax                          = getBuiltin builtinLevelMax
primSetOmega                          = getBuiltin builtinSetOmega
primFromNat                           = getBuiltin builtinFromNat
primFromNeg                           = getBuiltin builtinFromNeg
primFromString                        = getBuiltin builtinFromString
primQName                             = getBuiltin builtinQName
primArg                               = getBuiltin builtinArg
primArgArg                            = getBuiltin builtinArgArg
primAbs                               = getBuiltin builtinAbs
primAbsAbs                            = getBuiltin builtinAbsAbs
primAgdaSort                          = getBuiltin builtinAgdaSort
primHiding                            = getBuiltin builtinHiding
primHidden                            = getBuiltin builtinHidden
primInstance                          = getBuiltin builtinInstance
primVisible                           = getBuiltin builtinVisible
primRelevance                         = getBuiltin builtinRelevance
primRelevant                          = getBuiltin builtinRelevant
primIrrelevant                        = getBuiltin builtinIrrelevant
primAssoc                             = getBuiltin builtinAssoc
primAssocLeft                         = getBuiltin builtinAssocLeft
primAssocRight                        = getBuiltin builtinAssocRight
primAssocNon                          = getBuiltin builtinAssocNon
primPrecedence                        = getBuiltin builtinPrecedence
primPrecRelated                       = getBuiltin builtinPrecRelated
primPrecUnrelated                     = getBuiltin builtinPrecUnrelated
primFixity                            = getBuiltin builtinFixity
primFixityFixity                      = getBuiltin builtinFixityFixity
primArgInfo                           = getBuiltin builtinArgInfo
primArgArgInfo                        = getBuiltin builtinArgArgInfo
primAgdaSortSet                       = getBuiltin builtinAgdaSortSet
primAgdaSortLit                       = getBuiltin builtinAgdaSortLit
primAgdaSortUnsupported               = getBuiltin builtinAgdaSortUnsupported
primAgdaTerm                          = getBuiltin builtinAgdaTerm
primAgdaTermVar                       = getBuiltin builtinAgdaTermVar
primAgdaTermLam                       = getBuiltin builtinAgdaTermLam
primAgdaTermExtLam                    = getBuiltin builtinAgdaTermExtLam
primAgdaTermDef                       = getBuiltin builtinAgdaTermDef
primAgdaTermCon                       = getBuiltin builtinAgdaTermCon
primAgdaTermPi                        = getBuiltin builtinAgdaTermPi
primAgdaTermSort                      = getBuiltin builtinAgdaTermSort
primAgdaTermLit                       = getBuiltin builtinAgdaTermLit
primAgdaTermUnsupported               = getBuiltin builtinAgdaTermUnsupported
primAgdaTermMeta                      = getBuiltin builtinAgdaTermMeta
primAgdaErrorPart                     = getBuiltin builtinAgdaErrorPart
primAgdaErrorPartString               = getBuiltin builtinAgdaErrorPartString
primAgdaErrorPartTerm                 = getBuiltin builtinAgdaErrorPartTerm
primAgdaErrorPartName                 = getBuiltin builtinAgdaErrorPartName
primAgdaLiteral                       = getBuiltin builtinAgdaLiteral
primAgdaLitNat                        = getBuiltin builtinAgdaLitNat
primAgdaLitWord64                     = getBuiltin builtinAgdaLitWord64
primAgdaLitFloat                      = getBuiltin builtinAgdaLitFloat
primAgdaLitChar                       = getBuiltin builtinAgdaLitChar
primAgdaLitString                     = getBuiltin builtinAgdaLitString
primAgdaLitQName                      = getBuiltin builtinAgdaLitQName
primAgdaLitMeta                       = getBuiltin builtinAgdaLitMeta
primAgdaPattern                       = getBuiltin builtinAgdaPattern
primAgdaPatCon                        = getBuiltin builtinAgdaPatCon
primAgdaPatVar                        = getBuiltin builtinAgdaPatVar
primAgdaPatDot                        = getBuiltin builtinAgdaPatDot
primAgdaPatLit                        = getBuiltin builtinAgdaPatLit
primAgdaPatProj                       = getBuiltin builtinAgdaPatProj
primAgdaPatAbsurd                     = getBuiltin builtinAgdaPatAbsurd
primAgdaClause                        = getBuiltin builtinAgdaClause
primAgdaClauseClause                  = getBuiltin builtinAgdaClauseClause
primAgdaClauseAbsurd                  = getBuiltin builtinAgdaClauseAbsurd
primAgdaDefinitionFunDef              = getBuiltin builtinAgdaDefinitionFunDef
primAgdaDefinitionDataDef             = getBuiltin builtinAgdaDefinitionDataDef
primAgdaDefinitionRecordDef           = getBuiltin builtinAgdaDefinitionRecordDef
primAgdaDefinitionDataConstructor     = getBuiltin builtinAgdaDefinitionDataConstructor
primAgdaDefinitionPostulate           = getBuiltin builtinAgdaDefinitionPostulate
primAgdaDefinitionPrimitive           = getBuiltin builtinAgdaDefinitionPrimitive
primAgdaDefinition                    = getBuiltin builtinAgdaDefinition
primAgdaMeta                          = getBuiltin builtinAgdaMeta
primAgdaTCM                           = getBuiltin builtinAgdaTCM
primAgdaTCMReturn                     = getBuiltin builtinAgdaTCMReturn
primAgdaTCMBind                       = getBuiltin builtinAgdaTCMBind
primAgdaTCMUnify                      = getBuiltin builtinAgdaTCMUnify
primAgdaTCMTypeError                  = getBuiltin builtinAgdaTCMTypeError
primAgdaTCMInferType                  = getBuiltin builtinAgdaTCMInferType
primAgdaTCMCheckType                  = getBuiltin builtinAgdaTCMCheckType
primAgdaTCMNormalise                  = getBuiltin builtinAgdaTCMNormalise
primAgdaTCMReduce                     = getBuiltin builtinAgdaTCMReduce
primAgdaTCMCatchError                 = getBuiltin builtinAgdaTCMCatchError
primAgdaTCMGetContext                 = getBuiltin builtinAgdaTCMGetContext
primAgdaTCMExtendContext              = getBuiltin builtinAgdaTCMExtendContext
primAgdaTCMInContext                  = getBuiltin builtinAgdaTCMInContext
primAgdaTCMFreshName                  = getBuiltin builtinAgdaTCMFreshName
primAgdaTCMDeclareDef                 = getBuiltin builtinAgdaTCMDeclareDef
primAgdaTCMDeclarePostulate           = getBuiltin builtinAgdaTCMDeclarePostulate
primAgdaTCMDefineFun                  = getBuiltin builtinAgdaTCMDefineFun
primAgdaTCMGetType                    = getBuiltin builtinAgdaTCMGetType
primAgdaTCMGetDefinition              = getBuiltin builtinAgdaTCMGetDefinition
primAgdaTCMQuoteTerm                  = getBuiltin builtinAgdaTCMQuoteTerm
primAgdaTCMUnquoteTerm                = getBuiltin builtinAgdaTCMUnquoteTerm
primAgdaTCMBlockOnMeta                = getBuiltin builtinAgdaTCMBlockOnMeta
primAgdaTCMCommit                     = getBuiltin builtinAgdaTCMCommit
primAgdaTCMIsMacro                    = getBuiltin builtinAgdaTCMIsMacro
primAgdaTCMWithNormalisation          = getBuiltin builtinAgdaTCMWithNormalisation
primAgdaTCMDebugPrint                 = getBuiltin builtinAgdaTCMDebugPrint
primAgdaTCMNoConstraints              = getBuiltin builtinAgdaTCMNoConstraints
primAgdaTCMRunSpeculative             = getBuiltin builtinAgdaTCMRunSpeculative

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

-- | Primitives with typechecking constrants.
constrainedPrims :: [String]
constrainedPrims =
  [ builtinConId
  , builtinPOr
  , builtinComp
  , builtinHComp
  , builtinTrans
  , builtin_glue
  , builtin_glueU
  ]

getNameOfConstrained :: HasBuiltins m => String -> m (Maybe QName)
getNameOfConstrained s = do
  unless (s `elem` constrainedPrims) __IMPOSSIBLE__
  getName' s
