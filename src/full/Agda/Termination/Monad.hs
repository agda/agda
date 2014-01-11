{-# LANGUAGE CPP, FlexibleInstances, TypeSynonymInstances, MultiParamTypeClasses,
      DeriveFunctor, GeneralizedNewtypeDeriving, StandaloneDeriving #-}

-- | The monad for the termination checker.
--
--   The termination monad @TerM@ is an extension of
--   the type checking monad 'TCM' by an environment
--   with information needed by the termination checker.

module Agda.Termination.Monad where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State

import Data.Functor ((<$>))

import Agda.Syntax.Abstract (QName,IsProjP(..))
import Agda.Syntax.Common   (Delayed(..))
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.Syntax.Position (noRange)

import Agda.Termination.CallGraph (CutOff(..),Order,le,unknown)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty

import Agda.Utils.Monad

#include "../undefined.h"
import Agda.Utils.Impossible

-- | The mutual block we are checking.
--
--   The functions are numbered according to their order of appearance
--   in this list.

type MutualNames = [QName]

-- | The target of the function we are checking.

type Target = QName

-- | The current guardedness level.

type Guarded = Order

-- | The termination environment.

data TerEnv = TerEnv

  -- First part: options, configuration.

  { terUseDotPatterns :: Bool
    -- ^ Are we mining dot patterns to find evindence of structal descent?
  , terGuardingTypeConstructors :: Bool
    -- ^ Do we assume that record and data type constructors
    --   preserve guardedness?
  , terSizeSuc :: Maybe QName
    -- ^ The name of size successor, if any.
  , terSharp   :: Maybe QName
    -- ^ The name of the delay constructor (sharp), if any.
  , terCutOff  :: CutOff
    -- ^ Depth at which to cut off the structural order.
    --   NOTE: No longer used, will disappear, after things have stabilized.

  -- Second part: accumulated info during descent into decls./term.
  , terCurrent :: QName
    -- ^ The name of the function we are currently checking.
  , terMutual  :: MutualNames
    -- ^ The names of the functions in the mutual block we are checking.
    --   This includes the internally generated functions
    --   (with, extendedlambda, coinduction).
  , terUserNames :: [QName]
    -- ^ The list of name actually appearing in the file (abstract syntax).
    --   Excludes the internally generated functions.
  , terTarget  :: Maybe Target
    -- ^ Target type of the function we are currently termination checking.
    --   Only the constructors of 'Target' are considered guarding.
  , terDelayed :: Delayed
    -- ^ Are we checking a delayed definition?
  , terPatterns :: [DeBruijnPat]
    -- ^ The patterns of the clause we are checking.
  , terPatternsRaise :: Int
    -- ^ Number of additional binders we have gone under
    --   (and consequently need to raise the patterns to compare to terms).
  , terGuarded :: Guarded
    -- ^ The current guardedness status.  Changes as we go deeper into the term.
  }

-- | An empty termination environment.
--
--   Values are set to a safe default meaning that with these
--   initial values the termination checker will not miss
--   termination errors it would have seen with better settings
--   of these values.
--
--   Values that do not have a safe default are set to
--   @__IMPOSSIBLE__@.

defaultTerEnv :: TerEnv
defaultTerEnv = TerEnv
  { terUseDotPatterns           = False -- must be False initially!
  , terGuardingTypeConstructors = False
  , terSizeSuc                  = Nothing
  , terSharp                    = Nothing
  , terCutOff                   = DontCutOff
  , terUserNames                = __IMPOSSIBLE__ -- needs to be set!
  , terMutual                   = __IMPOSSIBLE__ -- needs to be set!
  , terCurrent                  = __IMPOSSIBLE__ -- needs to be set!
  , terTarget                   = Nothing
  , terDelayed                  = NotDelayed
  , terPatterns                 = __IMPOSSIBLE__ -- needs to be set!
  , terPatternsRaise            = 0
  , terGuarded                  = le -- not initially guarded
  }

-- | Termination monad service class.

class (Functor m, Monad m) => MonadTer m where
  terAsk   :: m TerEnv
  terLocal :: (TerEnv -> TerEnv) -> m a -> m a

  terAsks :: (TerEnv -> a) -> m a
  terAsks f = f <$> terAsk

-- | Termination monad.

newtype TerM a = TerM { terM :: ReaderT TerEnv TCM a }
  deriving (Functor, Applicative, Monad)

runTerm :: TerEnv -> TerM a -> TCM a
runTerm tenv (TerM m) = runReaderT m tenv

instance MonadTer TerM where
  terAsk     = TerM $ ask
  terLocal f = TerM . local f . terM

-- * Termination monad is a 'MonadTCM'.

instance MonadReader TCEnv TerM where
  ask       = TerM $ lift $ ask
  local f m = TerM $ ReaderT $ local f . runReaderT (terM m)

instance MonadState TCState TerM where
  get     = TerM $ lift $ get
  put     = TerM . lift . put

instance MonadIO TerM where
  liftIO = TerM . liftIO

instance MonadTCM TerM where
  liftTCM = TerM . lift

instance MonadError TCErr TerM where
  throwError = liftTCM . throwError
  catchError m handler = TerM $ ReaderT $ \ tenv -> do
    runTerm tenv m `catchError` (\ err -> runTerm tenv $ handler err)

-- * Modifiers and accessors for the termination environment in the monad.

terGetGuardingTypeConstructors :: TerM Bool
terGetGuardingTypeConstructors = terAsks terGuardingTypeConstructors

terGetUseDotPatterns :: TerM Bool
terGetUseDotPatterns = terAsks terUseDotPatterns

terSetUseDotPatterns :: Bool -> TerM a -> TerM a
terSetUseDotPatterns b = terLocal $ \ e -> e { terUseDotPatterns = b }

terGetSizeSuc :: TerM (Maybe QName)
terGetSizeSuc = terAsks terSizeSuc

terGetCurrent :: TerM QName
terGetCurrent = terAsks terCurrent

terSetCurrent :: QName -> TerM a -> TerM a
terSetCurrent q = terLocal $ \ e -> e { terCurrent = q }

terGetSharp :: TerM (Maybe QName)
terGetSharp = terAsks terSharp

terGetCutOff :: TerM CutOff
terGetCutOff = terAsks terCutOff

terGetMutual :: TerM MutualNames
terGetMutual = terAsks terMutual

terGetUserNames :: TerM [QName]
terGetUserNames = terAsks terUserNames

terGetTarget :: TerM (Maybe Target)
terGetTarget = terAsks terTarget

terSetTarget :: Maybe Target -> TerM a -> TerM a
terSetTarget t = terLocal $ \ e -> e { terTarget = t }

terGetDelayed :: TerM Delayed
terGetDelayed = terAsks terDelayed

terSetDelayed :: Delayed -> TerM a -> TerM a
terSetDelayed b = terLocal $ \ e -> e { terDelayed = b }

terGetPatterns :: TerM DeBruijnPats
terGetPatterns = raiseDBP <$> terAsks terPatternsRaise <*> terAsks terPatterns

terSetPatterns :: DeBruijnPats -> TerM a -> TerM a
terSetPatterns ps = terLocal $ \ e -> e { terPatterns = ps }

terRaise :: TerM a -> TerM a
terRaise = terLocal $ \ e -> e { terPatternsRaise = terPatternsRaise e + 1 }

terGetGuarded :: TerM Guarded
terGetGuarded = terAsks terGuarded

terModifyGuarded :: (Order -> Order) -> TerM a -> TerM a
terModifyGuarded f = terLocal $ \ e -> e { terGuarded = f $ terGuarded e }

terSetGuarded :: Order -> TerM a -> TerM a
terSetGuarded = terModifyGuarded . const

terUnguarded :: TerM a -> TerM a
terUnguarded = terSetGuarded unknown

-- | Should the codomain part of a function type preserve guardedness?
terPiGuarded :: TerM a -> TerM a
terPiGuarded m = ifM terGetGuardingTypeConstructors m $ terUnguarded m


-- * De Bruijn patterns.

type DeBruijnPats = [DeBruijnPat]

-- | Patterns with variables as de Bruijn indices.
type DeBruijnPat = DeBruijnPat' Int

data DeBruijnPat' a
  = VarDBP a
    -- ^ De Bruijn Index.
  | ConDBP QName [DeBruijnPat' a]
    -- ^ The name refers to either an ordinary
    --   constructor or the successor function on sized types.
  | LitDBP Literal
  | ProjDBP QName
  deriving (Functor, Show)

instance IsProjP (DeBruijnPat' a) where
  isProjP (ProjDBP d) = Just d
  isProjP _           = Nothing

instance PrettyTCM DeBruijnPat where
  prettyTCM (VarDBP i)    = text $ show i
  prettyTCM (ConDBP c ps) = parens (prettyTCM c <+> hsep (map prettyTCM ps))
  prettyTCM (LitDBP l)    = prettyTCM l
  prettyTCM (ProjDBP d)   = prettyTCM d

-- | A dummy pattern used to mask a pattern that cannot be used
--   for structural descent.

unusedVar :: DeBruijnPat
unusedVar = LitDBP (LitString noRange "term.unused.pat.var")

-- | @raiseDBP n ps@ increases each de Bruijn index in @ps@ by @n@.
--   Needed when going under a binder during analysis of a term.

raiseDBP :: Int -> DeBruijnPats -> DeBruijnPats
raiseDBP 0 = id
raiseDBP n = map $ fmap (n +)
