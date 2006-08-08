{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}
module TypeChecking.Monad.Base where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Reader
import Control.Exception
import Data.Map as Map
import Data.Generics
import Data.FunctorM

import Syntax.Common
import qualified Syntax.Abstract as A
import Syntax.Internal
import Syntax.Internal.Debug ()
import Syntax.Position
import Syntax.Scope
import Syntax.Info (NameInfo)

import Interaction.Exceptions
import Interaction.Options

import Utils.Fresh
import Utils.Monad
import Utils.Monad.Undo
import Utils.Trace

---------------------------------------------------------------------------
-- * Type checking state
---------------------------------------------------------------------------

data TCState =
    TCSt { stFreshThings       :: FreshThings
	 , stMetaStore	       :: MetaStore
	 , stInteractionPoints :: InteractionPoints
	 , stConstraints       :: Constraints
	 , stSignature	       :: Signature
	 , stScopeInfo	       :: ScopeInfo
	 , stOptions	       :: CommandLineOptions
	 , stStatistics	       :: Statistics
	 , stTrace	       :: CallTrace
	     -- ^ record what is happening (for error msgs)
	 }

data FreshThings =
	Fresh { fMeta	     :: MetaId
	      , fInteraction :: InteractionId
	      , fName	     :: NameId
	      , fConstraint  :: ConstraintId
	      }
    deriving (Show)

initState :: TCState
initState =
    TCSt { stFreshThings       = Fresh 0 0 0 0
	 , stMetaStore	       = Map.empty
	 , stInteractionPoints = Map.empty
	 , stConstraints       = Map.empty
	 , stSignature	       = Map.empty
	 , stScopeInfo	       = emptyScopeInfo_
	 , stOptions	       = defaultOptions
	 , stStatistics	       = Map.empty
	 , stTrace	       = noTrace
	 }

instance HasFresh MetaId FreshThings where
    nextFresh s = (i, s { fMeta = i + 1 })
	where
	    i = fMeta s

instance HasFresh InteractionId FreshThings where
    nextFresh s = (i, s { fInteraction = i + 1 })
	where
	    i = fInteraction s

-- Name ids are always even. Makes sure that there are no clashes with names
-- generated during scope checking (which are always odd).
instance HasFresh NameId FreshThings where
    nextFresh s = (2 * i, s { fName = i + 1 })
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
-- ** Closure
---------------------------------------------------------------------------

data Closure a = Closure { clSignature  :: Signature
			 , clEnv	:: TCEnv
			 , clScope	:: ScopeInfo
			 , clValue	:: a
			 }
    deriving (Typeable, Data)

instance HasRange a => HasRange (Closure a) where
    getRange = getRange . clValue

---------------------------------------------------------------------------
-- ** Constraints
---------------------------------------------------------------------------

newtype ConstraintId = CId Nat
    deriving (Eq, Ord, Num, Typeable, Data)

instance Show ConstraintId where
    show (CId x) = show x

type ConstraintClosure = Closure Constraint

data Constraint = ValueEq Type Term Term
		| TypeEq Type Type
		| SortLeq Sort Sort
		| SortEq Sort Sort
  deriving (Typeable, Data)

instance Show Constraint where
    show (ValueEq t u v) = show u ++ "  =  " ++ show v ++ "  :  " ++ show t
    show (TypeEq a b)	 = show a ++ "  =  " ++ show b
    show (SortEq a b)	 = show a ++ "  =  " ++ show b
    show (SortLeq a b)	 = show a ++ "  <=  " ++ show b

type Constraints = Map ConstraintId ConstraintClosure

---------------------------------------------------------------------------
-- * Judgements
---------------------------------------------------------------------------

data Judgement t s a
	= HasType a t
	| IsType  a s
	| IsSort  a
    deriving (Typeable, Data)

instance (Show t, Show s, Show a) => Show (Judgement t s a) where
    show (HasType a t) = show a ++ " : " ++ show t
    show (IsType  a s) = show a ++ " type " ++ show s
    show (IsSort  a)   = show a ++ " sort"

instance Functor (Judgement t s) where
    fmap f (HasType x t) = HasType (f x) t
    fmap f (IsType  x s) = IsType (f x) s
    fmap f (IsSort  x)	 = IsSort (f x)

instance FunctorM (Judgement t s) where
    fmapM f (HasType x t) = flip HasType t <$> f x
    fmapM f (IsType  x s) = flip IsType s <$> f x
    fmapM f (IsSort  x)   = IsSort <$> f x

---------------------------------------------------------------------------
-- ** Meta variables
---------------------------------------------------------------------------

data MetaVariable = 
	MetaVar	{ getMetaInfo	  :: MetaInfo
		, mvJudgement	  :: Judgement Type Sort MetaId
		, mvInstantiation :: MetaInstantiation
		}
    deriving (Typeable, Data)

data MetaInstantiation
	= InstV Term
	| InstT Type
	| InstS Sort
	| Open
    deriving (Typeable, Data)

-- | TODO: Not so nice.
type MetaInfo = Closure Range

type MetaStore = Map MetaId MetaVariable

instance HasRange MetaVariable where
    getRange m = getRange $ getMetaInfo m

instance Show MetaVariable where
    show mv =
	case mv of
	    MetaVar mi j i  -> show j ++ show i ++ r
	where
	    r = " [" ++ show (getRange mv) ++ "]"

instance Show MetaInstantiation where
    show (InstV v) = " := " ++ show v
    show (InstT t) = " := " ++ show t
    show (InstS s) = " := " ++ show s
    show  Open	   = ""

getMetaScope :: MetaVariable -> ScopeInfo
getMetaScope m = clScope $ getMetaInfo m

getMetaEnv :: MetaVariable -> TCEnv
getMetaEnv m = clEnv $ getMetaInfo m

getMetaSig :: MetaVariable -> Signature
getMetaSig m = clSignature $ getMetaInfo m 

setRange :: MetaVariable -> Range -> MetaVariable
setRange (MetaVar mi j inst) r = MetaVar (mi {clValue = r}) j inst

---------------------------------------------------------------------------
-- ** Interaction meta variables
---------------------------------------------------------------------------

type InteractionPoints = Map InteractionId MetaId

newtype InteractionId = InteractionId Nat
    deriving (Eq,Ord,Num)

instance Show InteractionId where
    show (InteractionId x) = "?" ++ show x

---------------------------------------------------------------------------
-- ** Signature
---------------------------------------------------------------------------

type Signature	 = Map ModuleName ModuleDef
type Definitions = Map Name Definition

data ModuleDef = ModuleDef
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
		     Sort
		     IsAbstract
	  | Constructor Nat	-- nof parameters
			QName	-- name of datatype
			IsAbstract
    deriving (Show, Typeable, Data)

defClauses :: Definition -> [Clause]
defClauses (Defn _ _ (Function cs _)) = cs
defClauses _			      = []


---------------------------------------------------------------------------
-- ** Statistics
---------------------------------------------------------------------------

type Statistics = Map String Int

---------------------------------------------------------------------------
-- ** Trace
---------------------------------------------------------------------------

type CallTrace = Trace (Closure Call)

noTrace :: CallTrace
noTrace = TopLevel []

data Call = CheckClause Type A.Clause (Maybe Clause)
	  | CheckPatterns [Arg A.Pattern] Type (Maybe ([String], [Arg Term], Type))
	  | CheckPattern String A.Pattern Type (Maybe ([String], Term))
	  | CheckLetBinding A.LetBinding (Maybe ())
	  | InferExpr A.Expr (Maybe (Term, Type))
	  | CheckExpr A.Expr Type (Maybe Term)
	  | WithMetaInfo MetaInfo (Maybe ())
	  | ForceSort Range Type (Maybe Sort)
	  | IsTypeCall A.Expr Sort (Maybe Type)
	  | IsType_ A.Expr (Maybe Type)
	  | InferVar Name (Maybe (Term, Type))
	  | InferDef NameInfo QName (Maybe (Term, Type))
	  | CheckArguments Range [Arg A.Expr] Type Type (Maybe Args)
    deriving (Typeable)

instance HasRange CallTrace where
    getRange (TopLevel _)      = noRange
    getRange (Current c _ _ _) = getRange c

instance HasRange Call where
    getRange (CheckClause _ c _)	= getRange c
    getRange (CheckPatterns ps _ _)	= getRange ps
    getRange (CheckPattern _ p _ _)	= getRange p
    getRange (InferExpr e _)		= getRange e
    getRange (CheckExpr e _ _)		= getRange e
    getRange (WithMetaInfo mi _)	= getRange mi
    getRange (CheckLetBinding b _)	= getRange b
    getRange (ForceSort r _ _)		= r
    getRange (IsTypeCall e s _)		= getRange e
    getRange (IsType_ e _)		= getRange e
    getRange (InferVar x _)		= getRange x
    getRange (InferDef _ f _)		= getRange f
    getRange (CheckArguments r _ _ _ _) = r

---------------------------------------------------------------------------
-- * Type checking environment
---------------------------------------------------------------------------

data TCEnv =
    TCEnv { envContext	     :: Context
	  , envLetBindings   :: LetBindings
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
		, envLetBindings   = Map.empty
		, envCurrentModule = noModuleName
		, envAbstractMode  = False
		}

---------------------------------------------------------------------------
-- ** Context
---------------------------------------------------------------------------

type Context = [(Name, Type)]

---------------------------------------------------------------------------
-- ** Let bindings
---------------------------------------------------------------------------

type LetBindings = Map Name (Term, Type)

---------------------------------------------------------------------------
-- * Type checking errors
---------------------------------------------------------------------------

data TCErr = Fatal CallTrace String
	   | Exception Range String
	   | PatternErr  TCState -- ^ for pattern violations
	   | AbortAssign TCState -- ^ used to abort assignment to meta when there are instantiations
  deriving (Typeable)

instance Error TCErr where
    noMsg    = Fatal noTrace ""
    strMsg s = Fatal noTrace s

instance Show TCErr where
    show (Fatal tr s)	 = show (getRange tr) ++ ": " ++ s
    show (Exception r s) = show r ++ ": " ++ s
    show (PatternErr _)  = "Pattern violation (you shouldn't see this)"
    show (AbortAssign _) = "Abort assignment (you shouldn't see this)"

patternViolation :: TCM a
patternViolation =
    do	s <- get
	throwError $ PatternErr s

---------------------------------------------------------------------------
-- * Type checking monad
---------------------------------------------------------------------------

type TCErrT = ErrorT TCErr
newtype TCM a = TCM { unTCM :: UndoT TCState (StateT TCState (ReaderT TCEnv (TCErrT IO))) a}
    deriving (MonadState TCState, MonadReader TCEnv, MonadError TCErr, MonadUndo TCState)

-- We want a special monad implementation of fail.
instance Monad TCM where
    return  = TCM . return
    m >>= k = TCM $ unTCM m >>= unTCM . k
    fail s  = TCM $ do	tr <- gets stTrace
			throwError $ Fatal tr s

instance MonadIO TCM where
  liftIO m = TCM $ do tr <- gets stTrace
                      lift $ lift $ lift $ ErrorT $
                        handle (return . throwError . Fatal tr . show)
                        (failOnException
                         (\r -> return . throwError . Exception r)
                         (return <$> m) )

-- | Running the type checking monad
runTCM :: TCM a -> IO (Either TCErr a)
runTCM m = runErrorT
	 $ flip runReaderT initEnv
	 $ flip evalStateT initState
	 $ runUndoT
	 $ unTCM m

