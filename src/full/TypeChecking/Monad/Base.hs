{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances -cpp #-}
module TypeChecking.Monad.Base where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Reader
import Control.Exception
import Data.Map as Map
import Data.Generics
import Data.FunctorM

import Syntax.Common
import qualified Syntax.Concrete as C
import qualified Syntax.Concrete.Definitions as D
import qualified Syntax.Abstract as A
import Syntax.Internal
import Syntax.Internal.Debug ()
import Syntax.Position
import Syntax.ScopeInfo

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
	 , stImports	       :: Signature
	 , stImportedModules   :: [ModuleName]
	 , stVisitedModules    :: [ModuleName]
	 , stScopeInfo	       :: ScopeInfo
	 , stOptions	       :: CommandLineOptions
	 , stStatistics	       :: Statistics
	 , stTrace	       :: CallTrace
	 , stBuiltinThings     :: BuiltinThings PrimFun
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
	 , stImports	       = Map.empty
	 , stImportedModules   = []
	 , stVisitedModules    = []
	 , stScopeInfo	       = emptyScopeInfo_
	 , stOptions	       = defaultOptions
	 , stStatistics	       = Map.empty
	 , stTrace	       = noTrace
	 , stBuiltinThings     = Map.empty
	 }

instance HasFresh MetaId FreshThings where
    nextFresh s = (i, s { fMeta = i + 1 })
	where
	    i = fMeta s

instance HasFresh InteractionId FreshThings where
    nextFresh s = (i, s { fInteraction = i + 1 })
	where
	    i = fInteraction s

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
-- ** Closure
---------------------------------------------------------------------------

data Closure a = Closure { clSignature  :: Signature
			 , clEnv	:: TCEnv
			 , clScope	:: ScopeInfo
			 , clTrace	:: CallTrace
			 , clValue	:: a
			 }
    deriving (Typeable)

instance HasRange a => HasRange (Closure a) where
    getRange = getRange . clValue

buildClosure :: a -> TCM (Closure a)
buildClosure x = do
    env   <- ask
    sig   <- gets stSignature
    scope <- gets stScopeInfo
    trace <- gets stTrace
    return $ Closure sig env scope trace x

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
    deriving (Typeable)

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
    deriving (Typeable, Data)

data Definition = Defn { defType     :: Type	-- type of the lifted definition
		       , defFreeVars :: Nat
		       , theDef	     :: Defn
		       }
    deriving (Typeable, Data)

data Defn = Axiom
	  | Function [Clause] IsAbstract
	  | Datatype Nat	-- nof parameters
		     [QName]	-- constructor names
		     Sort
		     IsAbstract
	  | Constructor Nat	-- nof parameters
			QName	-- name of datatype
			IsAbstract
	  | Primitive IsAbstract String -- PrimFun
    deriving (Typeable, Data)

data Reduced no yes = NoReduction no | YesReduction yes
    deriving (Typeable)

data PrimFun = PrimFun
	{ primFunArity		:: Arity
	, primFunImplementation :: [Arg Term] -> TCM (Reduced [Arg Term] Term)
	}
    deriving (Typeable)

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
	  | CheckPatterns [Arg A.Pattern] Type (Maybe ([String], [Arg Pattern], [Arg Term], Type))
	  | CheckPattern String A.Pattern Type (Maybe ([String], Pattern, Term))
	  | CheckLetBinding A.LetBinding (Maybe ())
	  | InferExpr A.Expr (Maybe (Term, Type))
	  | CheckExpr A.Expr Type (Maybe Term)
	  | IsTypeCall A.Expr Sort (Maybe Type)
	  | IsType_ A.Expr (Maybe Type)
	  | InferVar Name (Maybe (Term, Type))
	  | InferDef Range QName (Maybe (Term, Type))
	  | CheckArguments Range [Arg A.Expr] Type Type (Maybe Args)
	  | CheckDataDef Range Name [A.LamBinding] [A.Constructor] (Maybe ())
	  | CheckConstructor QName Telescope Sort A.Constructor (Maybe ())
	  | CheckFunDef Range Name [A.Clause] (Maybe ())
	  | CheckPragma Range A.Pragma (Maybe ())
	  | CheckPrimitive Range Name A.Expr (Maybe ())
    deriving (Typeable)

instance HasRange a => HasRange (Trace a) where
    getRange (TopLevel _)      = noRange
    getRange (Current c _ _ _) = getRange c

instance HasRange Call where
    getRange (CheckClause _ c _)	  = getRange c
    getRange (CheckPatterns ps _ _)	  = getRange ps
    getRange (CheckPattern _ p _ _)	  = getRange p
    getRange (InferExpr e _)		  = getRange e
    getRange (CheckExpr e _ _)		  = getRange e
    getRange (CheckLetBinding b _)	  = getRange b
    getRange (IsTypeCall e s _)		  = getRange e
    getRange (IsType_ e _)		  = getRange e
    getRange (InferVar x _)		  = getRange x
    getRange (InferDef _ f _)		  = getRange f
    getRange (CheckArguments r _ _ _ _)   = r
    getRange (CheckDataDef i _ _ _ _)	  = getRange i
    getRange (CheckConstructor _ _ _ c _) = getRange c
    getRange (CheckFunDef i _ _ _)	  = getRange i
    getRange (CheckPragma r _ _)	  = r
    getRange (CheckPrimitive i _ _ _)	  = getRange i

---------------------------------------------------------------------------
-- ** Builtin things
---------------------------------------------------------------------------

type BuiltinThings pf = Map String (Builtin pf)

data Builtin pf
	= Builtin Term
	| Prim pf
    deriving (Show)

instance Functor Builtin where
    fmap f (Builtin t) = Builtin t
    fmap f (Prim x)    = Prim $ f x

instance FunctorM Builtin where
    fmapM f (Builtin t) = return $ Builtin t
    fmapM f (Prim x)    = Prim <$> f x

---------------------------------------------------------------------------
-- * Type checking environment
---------------------------------------------------------------------------

data TCEnv =
    TCEnv { envContext	     :: Context
	  , envLetBindings   :: LetBindings
	  , envCurrentModule :: ModuleName
	  , envImportPath    :: [ModuleName]	-- ^ to detect import cycles
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
		, envImportPath	   = []
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

data TypeError
	= InternalError String
	| NotImplemented String
	| PropMustBeSingleton
	| ShouldEndInApplicationOfTheDatatype Type
	    -- ^ The target of a constructor isn't an application of its
	    -- datatype. The 'Type' records what it does target.
	| ShouldBeAppliedToTheDatatypeParameters Term Term
	    -- ^ The target of a constructor isn't its datatype applied to
	    --	 something that isn't the parameters. First term is the correct
	    --	 target and the second term is the actual target.
	| ShouldBeApplicationOf Type QName
	    -- ^ Expected a type to be an application of a particular datatype.
	| DifferentArities
	    -- ^ Varying number of arguments for a function.
	| WrongHidingInLHS Type
	    -- ^ The left hand side of a function defintion has a hidden argument
	    --	 where a non-hidden was expected.
	| WrongHidingInLambda Type
	    -- ^ Expected a non-hidden function and found a hidden lambda.
	| WrongHidingInApplication Type
	    -- ^ A function is applied to a hidden argument where a non-hidden was expected.
	| ShouldBeEmpty Type
	| ShouldBeASort Type
	    -- ^ The given type should have been a sort.
	| ShouldBePi Type
	    -- ^ The given type should have been a pi.
	| NotAProperTerm
	| UnequalTerms Term Term Type
	| UnequalTypes Type Type
	| UnequalHiding Type Type
	    -- ^ The two function types have different hiding.
	| UnequalSorts Sort Sort
	| NotLeqSort Sort Sort
	| MetaCannotDependOn MetaId [Int] Int
	    -- ^ The arguments are the meta variable, the parameters it can
	    --	 depend on and the paratemeter that it wants to depend on.
	| MetaOccursInItself MetaId
	| GenericError String
	| NoSuchBuiltinName String
	| DuplicateBuiltinBinding String Term Term
	| NoBindingForBuiltin String
	| NoSuchPrimitiveFunction String
	| BuiltinInParameterisedModule String
	| NoRHSRequiresAbsurdPattern [Arg A.Pattern]
    -- Import errors
	| LocalVsImportedModuleClash ModuleName
	| UnsolvedMetasInImport [Range]
	| CyclicModuleDependency [ModuleName]
	| FileNotFound ModuleName [FilePath]
	| ClashingFileNamesFor ModuleName [FilePath]
    -- Scope errors
	| NotInScope [C.QName]
	| NoSuchModule C.QName
	| UninstantiatedModule C.QName
	| ClashingDefinition C.Name A.QName
	| ClashingModule A.ModuleName A.ModuleName
	| ClashingImport C.Name A.QName
	| ClashingModuleImport C.Name A.ModuleName
	| ModuleDoesntExport A.ModuleName [C.ImportedName]
    -- Concrete to Abstract errors
	| HigherOrderPattern C.Pattern C.Pattern
	    -- ^ the first pattern is an application and the second
	    --	 pattern is the function part (and it's not
	    --	 a constructor pattern).
	| NotAModuleExpr C.Expr
	    -- ^ The expr was used in the right hand side of an implicit module
	    --	 definition, but it wasn't of the form @m Delta@.
	| NoTopLevelModule C.Declaration
	| NotAnExpression C.Expr
	| NotAValidLetBinding D.NiceDeclaration
	| NotAValidLHS C.Pattern
	| NothingAppliedToHiddenArg C.Expr
	| NothingAppliedToHiddenPat C.Pattern
    -- Operator errors
	| NoParseForApplication [C.Expr]
	| AmbiguousParseForApplication [C.Expr] [C.Expr]
	| NoParseForLHS C.Pattern
	| AmbiguousParseForLHS C.Pattern [C.Pattern]
    deriving (Typeable)

data TCErr = TypeError TCState (Closure TypeError)
	   | Exception Range String
	   | PatternErr  TCState -- ^ for pattern violations
	   | AbortAssign TCState -- ^ used to abort assignment to meta when there are instantiations
  deriving (Typeable)

instance Error TCErr where
    noMsg  = strMsg ""
    strMsg = Exception noRange . strMsg

{-
instance Show TCErr where
    show (TypeError _ e) = show (getRange $ clTrace e) ++ ": " ++ show (clValue e)
    show (Exception r s) = show r ++ ": " ++ s
    show (PatternErr _)  = "Pattern violation (you shouldn't see this)"
    show (AbortAssign _) = "Abort assignment (you shouldn't see this)"
-}

instance HasRange TCErr where
    getRange (TypeError _ cl) = getRange $ clTrace cl
    getRange (Exception r _)  = r
    getRange (PatternErr s)   = getRange $ stTrace s
    getRange (AbortAssign s)  = getRange $ stTrace s

---------------------------------------------------------------------------
-- * Type checking monad
---------------------------------------------------------------------------

newtype TCM a = TCM { unTCM :: UndoT TCState
			      (StateT TCState
			      (ReaderT TCEnv
			      (ErrorT TCErr IO))) a
		    }
#ifndef __HADDOCK__
    deriving (MonadState TCState, MonadReader TCEnv, MonadError TCErr, MonadUndo TCState)
#endif

patternViolation :: TCM a
patternViolation = do
    s <- get
    throwError $ PatternErr s

internalError :: String -> TCM a
internalError s = typeError $ InternalError s

typeError :: TypeError -> TCM a
typeError err = do
    cl <- buildClosure err
    s  <- get
    throwError $ TypeError s cl

handleTypeErrorException :: IO a -> TCM a
handleTypeErrorException m = do
    r <- liftIO $ liftM Right m `catchDyn` (return . Left)
    either typeError return r

-- We want a special monad implementation of fail.
instance Monad TCM where
    return  = TCM . return
    m >>= k = TCM $ unTCM m >>= unTCM . k
    fail    = internalError

instance MonadIO TCM where
  liftIO m = TCM $ do tr <- gets stTrace
                      lift $ lift $ lift $ ErrorT $
                        handle (return . throwError . Exception (getRange tr) . show)
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

