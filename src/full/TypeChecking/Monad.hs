{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}
module TypeChecking.Monad where

import Data.Map as Map

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Reader
import Data.Generics


import Syntax.Common
import Syntax.Info
import Syntax.Internal
import Syntax.Internal.Debug ()
import Syntax.Position
import Syntax.Scope

import Utils.Fresh

---------------------------------------------------------------------------
-- * Type checking state
---------------------------------------------------------------------------

data TCState =
    TCSt { stFreshThings    :: FreshThings
	 , stMetaStore	    :: MetaStore
	 , stConstraints    :: Constraints
	 , stSignature	    :: Signature
	 , stScopeInfo	    :: ScopeInfo
	 , stTrace	    :: Trace
	    -- ^ record what is happening (for error msgs)
	 }

data FreshThings =
	Fresh { fMeta	    :: MetaId
	      , fName	    :: NameId
	      , fConstraint :: ConstraintId
	      }
    deriving (Show)

initState :: TCState
initState =
    TCSt { stFreshThings = Fresh 0 0 0
	 , stMetaStore	 = Map.empty
	 , stConstraints = Map.empty
	 , stSignature   = Map.empty
	 , stScopeInfo	 = emptyScopeInfo_
	 , stTrace	 = noTrace
	 }

instance HasFresh MetaId FreshThings where
    nextFresh s = (i, s { fMeta = i + 1 })
	where
	    i = fMeta s

instance HasFresh NameId FreshThings where
    nextFresh s = (i, s { fName = i + 1 })
	where
	    i = fName s

instance HasFresh ConstraintId FreshThings where
    nextFresh s = (i, s { fConstraint = i + 1 })
	where
	    i = fConstraint s

instance HasFresh i FreshThings => HasFresh i TCState where
    nextFresh s = (i, s { stFreshThings = f })
	where
	    (i,f) = nextFresh $ stFreshThings s

---------------------------------------------------------------------------
-- ** Constraints
---------------------------------------------------------------------------

newtype ConstraintId = CId Nat
    deriving (Eq, Ord, Show, Num, Typeable, Data)

data Constraint = ValueEq Type Term Term
		| TypeEq Type Type
  deriving (Show, Typeable, Data)

type Constraints = Map ConstraintId (Signature,TCEnv,Constraint)

---------------------------------------------------------------------------
-- ** Meta variables
---------------------------------------------------------------------------

data MetaVariable = InstV MetaInfo Term Type
                  | InstT MetaInfo Type
                  | InstS MetaInfo Sort
                  | UnderScoreV MetaInfo Type [ConstraintId]
                  | UnderScoreT MetaInfo Sort [ConstraintId]
                  | UnderScoreS MetaInfo      [ConstraintId]
                  | HoleV       MetaInfo Type [ConstraintId]
                  | HoleT       MetaInfo Sort [ConstraintId]
  deriving (Typeable, Data)

type MetaStore = Map MetaId MetaVariable

instance HasRange MetaVariable where
    getRange m = getRange $ getMetaInfo m

instance Show MetaVariable where
    show mv =
	case mv of
	    InstV _ v t -> r ++ " := " ++ show v ++ " : " ++ show t
	    InstT _ t	-> r ++ " := " ++ show t
	    InstS _ s	-> r ++ " := " ++ show s
	    UnderScoreV _ t _	-> r ++ " : " ++ show t
	    UnderScoreT _ s _	-> r ++ " type " ++ show s
	    UnderScoreS _ _	-> r ++ " sort"
	    HoleV _ t _		-> r ++ " : " ++ show t
	    HoleT _ s _		-> r ++ " type " ++ show s
	where
	    r = "(" ++ show (getRange mv) ++ ")"

getMetaScope :: MetaVariable -> ScopeInfo
getMetaScope m = metaScope $ getMetaInfo m

 
getMetaInfo :: MetaVariable -> MetaInfo
getMetaInfo m = 
     case m of
	InstV i _ _	  -> i
	InstT i _	  -> i
	InstS i _	  -> i
	UnderScoreV i _ _ -> i
	UnderScoreT i _ _ -> i
	UnderScoreS i _   -> i
	HoleV i _ _	  -> i
	HoleT i _ _	  -> i



---------------------------------------------------------------------------
-- ** Signature
---------------------------------------------------------------------------

type Signature	 = Map ModuleName ModuleDef
type Definitions = Map Name Definition

data ModuleDef = MDef { mdefName       :: ModuleName
		      , mdefTelescope  :: Telescope
		      , mdefNofParams  :: Nat
		      , mdefModuleName :: ModuleName
		      , mdefArgs       :: Args
		      }
	       | MExplicit
		      { mdefName       :: ModuleName
		      , mdefTelescope  :: Telescope
		      , mdefNofParams  :: Nat
		      , mdefDefs       :: Definitions
		      }
    deriving (Show, Typeable, Data)

data Definition = Defn { defType     :: Type	-- type of the lifted definition
		       , defFreeVars :: Nat
		       , theDef	     :: Defn
		       }
    deriving (Show, Typeable, Data)

data Defn = Axiom
	  | Function [Clause] IsAbstract
	  | Datatype Nat	-- nof parameters
		     [QName]	-- constructor names
		     IsAbstract
	  | Constructor Nat	-- nof parameters
			QName	-- name of datatype
			IsAbstract
    deriving (Show, Typeable, Data)

defClauses :: Definition -> [Clause]
defClauses (Defn _ _ (Function cs _)) = cs
defClauses _			      = []


---------------------------------------------------------------------------
-- * Trace
---------------------------------------------------------------------------

-- | The trace is just a range at the moment.
newtype Trace = Trace { traceRange :: Range }

noTrace :: Trace
noTrace = Trace noRange

instance HasRange Trace where
    getRange (Trace r) = r

---------------------------------------------------------------------------
-- * Type checking environment
---------------------------------------------------------------------------

data TCEnv =
    TCEnv { envContext	     :: Context
	  , envCurrentModule :: ModuleName
	  , envAbstractMode  :: Bool
		-- ^ When checking the typesignature of a public definition
		--   or the body of a non-abstract definition this is true.
		--   To prevent information about abstract things leaking
		--   outside the module.
	  }
    deriving (Typeable, Data, Show)

initEnv :: TCEnv
initEnv = TCEnv { envContext	   = []
		, envCurrentModule = noModuleName
		, envAbstractMode  = False
		}

---------------------------------------------------------------------------
-- ** Context
---------------------------------------------------------------------------

type Context = [(Name, Type)]

---------------------------------------------------------------------------
-- * Type checking errors
---------------------------------------------------------------------------

data TCErr = Fatal Range String
	   | PatternErr [MetaId] -- ^ for pattern violations, carries involved metavars
  deriving Show

instance Error TCErr where
    noMsg    = Fatal noRange ""
    strMsg s = Fatal noRange s

patternViolation mIds = throwError $ PatternErr mIds

---------------------------------------------------------------------------
-- * Type checking monad
---------------------------------------------------------------------------

type TCErrT = ErrorT TCErr
newtype TCM a = TCM { unTCM :: StateT TCState (ReaderT TCEnv (TCErrT IO)) a }
    deriving (MonadState TCState, MonadReader TCEnv, MonadError TCErr, MonadIO)

-- We want a special monad implementation of fail.
instance Monad TCM where
    return  = TCM . return
    m >>= k = TCM $ unTCM m >>= unTCM . k
    fail s  = TCM $ do	r <- gets $ getRange . stTrace
			throwError $ Fatal r s

-- | Running the type checking monad
runTCM :: TCM a -> IO (Either TCErr a)
runTCM m = runErrorT
	 $ flip runReaderT initEnv
	 $ flip evalStateT initState
	 $ unTCM m

