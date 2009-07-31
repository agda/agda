{-# LANGUAGE CPP, ExistentialQuantification, FlexibleContexts, Rank2Types,
             TypeSynonymInstances, MultiParamTypeClasses, FlexibleInstances,
             UndecidableInstances, DeriveDataTypeable, GeneralizedNewtypeDeriving
  #-}
module Agda.TypeChecking.Monad.Base where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Reader
import Control.OldException
import Control.Applicative
import Data.Map as Map
import Data.Set as Set
import Data.Generics
import Data.Foldable
import Data.Traversable
import System.Time

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Concrete.Definitions as D
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.Interaction.Exceptions
import Agda.Interaction.Options
import qualified Agda.Interaction.Highlighting.Range as R
import Agda.Interaction.Highlighting.Precise (HighlightingInfo)

import Agda.Utils.Fresh
import Agda.Utils.Monad
import Agda.Utils.Monad.Undo
import Agda.Utils.Trace

#include "../../undefined.h"
import Agda.Utils.Impossible

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
	 , stImportedModules   :: Set ModuleName
	 , stVisitedModules    :: VisitedModules
	 , stDecodedModules    :: DecodedModules
         , stCurrentModule     :: Maybe ModuleName
           -- ^ The current module is available after it has been type
           -- checked.
	 , stScope	       :: ScopeInfo
	 , stOptions	       :: CommandLineOptions
	 , stStatistics	       :: Statistics
	 , stTrace	       :: CallTrace
	     -- ^ record what is happening (for error msgs)
	 , stMutualBlocks      :: Map MutualId (Set QName)
	 , stLocalBuiltins     :: BuiltinThings PrimFun
         , stImportedBuiltins  :: BuiltinThings PrimFun
         , stHaskellImports    :: [String]  -- ^ imports that should be generated
                                            --   by the compiler
	 }

data FreshThings =
	Fresh { fMeta	     :: MetaId
	      , fInteraction :: InteractionId
	      , fMutual	     :: MutualId
	      , fName	     :: NameId
	      , fCtx	     :: CtxId
              , fInteger     :: Integer
                -- ^ Can be used for various things.
	      }
    deriving (Show)

initState :: TCState
initState =
    TCSt { stFreshThings       = Fresh 0 0 0 (NameId 0 0) 0 0
	 , stMetaStore	       = Map.empty
	 , stInteractionPoints = Map.empty
	 , stConstraints       = []
	 , stSignature	       = emptySignature
	 , stImports	       = emptySignature
	 , stImportedModules   = Set.empty
	 , stVisitedModules    = Map.empty
	 , stDecodedModules    = Map.empty
         , stCurrentModule     = Nothing
	 , stScope	       = emptyScopeInfo
	 , stOptions	       = defaultOptions
	 , stStatistics	       = Map.empty
	 , stTrace	       = noTrace
	 , stMutualBlocks      = Map.empty
	 , stLocalBuiltins     = Map.empty
	 , stImportedBuiltins  = Map.empty
         , stHaskellImports    = []
	 }

stBuiltinThings :: TCState -> BuiltinThings PrimFun
stBuiltinThings s = stLocalBuiltins s `Map.union` stImportedBuiltins s

instance HasFresh MetaId FreshThings where
    nextFresh s = (i, s { fMeta = i + 1 })
	where
	    i = fMeta s

instance HasFresh MutualId FreshThings where
    nextFresh s = (i, s { fMutual = i + 1 })
	where
	    i = fMutual s

instance HasFresh InteractionId FreshThings where
    nextFresh s = (i, s { fInteraction = i + 1 })
	where
	    i = fInteraction s

instance HasFresh NameId FreshThings where
    nextFresh s = (i, s { fName = succ i })
	where
	    i = fName s

instance HasFresh CtxId FreshThings where
    nextFresh s = (i, s { fCtx = succ i })
	where
	    i = fCtx s

instance HasFresh Integer FreshThings where
    nextFresh s = (i, s { fInteger = succ i })
	where
	    i = fInteger s

instance HasFresh i FreshThings => HasFresh i TCState where
    nextFresh s = (i, s { stFreshThings = f })
	where
	    (i,f) = nextFresh $ stFreshThings s

---------------------------------------------------------------------------
-- ** Interface
---------------------------------------------------------------------------

type VisitedModules = Map C.TopLevelModuleName (Interface, ClockTime)
type DecodedModules = Map C.TopLevelModuleName (Interface, ClockTime)

data Interface = Interface
	{ iImportedModules :: [ModuleName]
        , iModuleName      :: ModuleName
	, iScope	   :: Map A.ModuleName Scope
        , iInsideScope     :: ScopeInfo
	, iSignature	   :: Signature
	, iBuiltin	   :: BuiltinThings String
        , iHaskellImports  :: [String]
        , iHighlighting    :: HighlightingInfo
	}
    deriving (Typeable, Data)

---------------------------------------------------------------------------
-- ** Closure
---------------------------------------------------------------------------

data Closure a = Closure { clSignature  :: Signature
			 , clEnv	:: TCEnv
			 , clScope	:: ScopeInfo
			 , clTrace	:: CallTrace
			 , clValue	:: a
			 }
    deriving (Typeable, Data)

instance HasRange a => HasRange (Closure a) where
    getRange = getRange . clValue

buildClosure :: MonadTCM tcm => a -> tcm (Closure a)
buildClosure x = liftTCM $ do
    env   <- ask
    sig   <- gets stSignature
    scope <- gets stScope
    trace <- gets stTrace
    return $ Closure sig env scope trace x

---------------------------------------------------------------------------
-- ** Constraints
---------------------------------------------------------------------------

type ConstraintClosure = Closure Constraint

data Constraint = ValueCmp Comparison Type Term Term
		| TypeCmp Comparison Type Type
                | TelCmp Comparison Telescope Telescope
		| SortCmp Comparison Sort Sort
		| UnBlock MetaId
		| Guarded Constraint Constraints
                | IsEmpty Type
  deriving (Typeable)

data Comparison = CmpEq | CmpLeq
  deriving (Eq, Typeable)

type Constraints = [ConstraintClosure]

---------------------------------------------------------------------------
-- * Open things
---------------------------------------------------------------------------

-- | A thing tagged with the context it came from.
data Open a = OpenThing [CtxId] a
    deriving (Typeable, Data)

---------------------------------------------------------------------------
-- * Judgements
---------------------------------------------------------------------------

data Judgement t a
	= HasType a t
	| IsSort  a
    deriving (Typeable, Data)

instance (Show t, Show a) => Show (Judgement t a) where
    show (HasType a t) = show a ++ " : " ++ show t
    show (IsSort  a)   = show a ++ " sort"

instance Functor (Judgement t) where
    fmap f (HasType x t) = HasType (f x) t
    fmap f (IsSort  x)	 = IsSort (f x)

instance Foldable (Judgement t) where
    foldr f z (HasType x _) = f x z
    foldr f z (IsSort  x)   = f x z

instance Traversable (Judgement t) where
    traverse f (HasType x t) = flip HasType t <$> f x
    traverse f (IsSort  x)   = IsSort <$> f x

---------------------------------------------------------------------------
-- ** Meta variables
---------------------------------------------------------------------------

data MetaVariable =
	MetaVar	{ mvInfo	  :: MetaInfo
		, mvPriority	  :: MetaPriority -- ^ some metavariables are more eager to be instantiated
		, mvJudgement	  :: Judgement Type MetaId
		, mvInstantiation :: MetaInstantiation
		, mvListeners	  :: Set MetaId	  -- ^ metavariables interested in what happens to this guy
		}
    deriving (Typeable)

data MetaInstantiation
	= InstV Term
	| InstS Sort
	| Open
	| BlockedConst Term
        | PostponedTypeCheckingProblem (Closure (A.Expr, Type, TCM Bool))
    deriving (Typeable)

instance Show MetaInstantiation where
  show (InstV t) = "InstV (" ++ show t ++ ")"
  show (InstS s) = "InstS (" ++ show s ++ ")"
  show Open      = "Open"
  show (BlockedConst t) = "BlockedConst (" ++ show t ++ ")"
  show (PostponedTypeCheckingProblem{}) = "PostponedTypeCheckingProblem (...)"

newtype MetaPriority = MetaPriority Int
    deriving (Eq, Ord, Show)

-- | TODO: Not so nice.
type MetaInfo = Closure Range

type MetaStore = Map MetaId MetaVariable

instance HasRange MetaVariable where
    getRange m = getRange $ getMetaInfo m

instance SetRange MetaVariable where
  setRange r (MetaVar mi p j inst ls) = MetaVar (mi {clValue = r}) p j inst ls

normalMetaPriority :: MetaPriority
normalMetaPriority = MetaPriority 0

lowMetaPriority :: MetaPriority
lowMetaPriority = MetaPriority (-10)

highMetaPriority :: MetaPriority
highMetaPriority = MetaPriority 10

getMetaInfo :: MetaVariable -> MetaInfo
getMetaInfo = mvInfo

getMetaScope :: MetaVariable -> ScopeInfo
getMetaScope m = clScope $ getMetaInfo m

getMetaEnv :: MetaVariable -> TCEnv
getMetaEnv m = clEnv $ getMetaInfo m

getMetaSig :: MetaVariable -> Signature
getMetaSig m = clSignature $ getMetaInfo m

---------------------------------------------------------------------------
-- ** Interaction meta variables
---------------------------------------------------------------------------

type InteractionPoints = Map InteractionId MetaId

newtype InteractionId = InteractionId Nat
    deriving (Eq,Ord,Num,Integral,Real,Enum)

instance Show InteractionId where
    show (InteractionId x) = "?" ++ show x

---------------------------------------------------------------------------
-- ** Signature
---------------------------------------------------------------------------

data Signature = Sig
      { sigSections    :: Sections
      , sigDefinitions :: Definitions
      }
  deriving (Typeable, Data)

type Sections	 = Map ModuleName Section
type Definitions = Map QName Definition

data Section = Section
      { secTelescope :: Telescope
      , secFreeVars  :: Nat	    -- ^ This is the number of parameters when
				    --	 we're inside the section and 0
				    --	 outside. It's used to know how much of
				    --	 the context to apply function from the
				    --	 section to when translating from
				    --	 abstract to internal syntax.
      }
  deriving (Typeable, Data)

emptySignature :: Signature
emptySignature = Sig Map.empty Map.empty

data DisplayForm = Display Nat [Term] DisplayTerm
		-- ^ The three arguments are:
		--
		--   * @n@: number of free variables;
		--
		--   * Patterns for arguments, one extra free var which
		--     represents pattern vars. There should @n@ of them.
		--
		--   * Display form. @n@ free variables.
  deriving (Typeable, Data, Show)

data DisplayTerm = DWithApp [DisplayTerm] Args
		 | DTerm Term
  deriving (Typeable, Data, Show)

defaultDisplayForm :: QName -> [Open DisplayForm]
defaultDisplayForm c = []

data Definition = Defn { defName     :: QName
		       , defType     :: Type	-- type of the lifted definition
		       , defDisplay  :: [Open DisplayForm]
		       , defMutual   :: MutualId
		       , theDef	     :: Defn
		       }
    deriving (Typeable, Data)

type HaskellCode = String
type HaskellType = String

data HaskellRepresentation
      = HsDefn HaskellType HaskellCode
      | HsType HaskellType
  deriving (Typeable, Data, Show)

data Polarity = Covariant | Contravariant | Invariant
  deriving (Typeable, Data, Show, Eq)

-- | 'Positive' means strictly positive and 'Negative' means not strictly
-- positive.
data Occurrence = Positive | Negative | Unused
  deriving (Typeable, Data, Show, Eq, Ord)

data Defn = Axiom
            { axHsDef   :: Maybe HaskellRepresentation
            }
	  | Function
            { funClauses        :: [Clause]
            , funInv            :: FunctionInverse
            , funPolarity       :: [Polarity]
            , funArgOccurrences :: [Occurrence]
            , funAbstr          :: IsAbstract
            , funDelayed        :: Delayed
              -- ^ Are the clauses of this definition delayed?
            }
	  | Datatype
            { dataPars           :: Nat           -- nof parameters
	    , dataIxs            :: Nat           -- nof indices
            , dataInduction      :: Induction  -- data or codata?
            , dataClause         :: (Maybe Clause) -- this might be in an instantiated module
            , dataCons           :: [QName]        -- constructor names
            , dataSort           :: Sort
            , dataPolarity       :: [Polarity]
            , dataArgOccurrences :: [Occurrence]
            , dataHsType         :: Maybe HaskellType
            , dataAbstr          :: IsAbstract
            }
	  | Record
            { recPars           :: Nat
            , recClause         :: Maybe Clause
            , recFields         :: [A.QName]
            , recTel            :: Telescope
            , recSort           :: Sort
            , recPolarity       :: [Polarity]
            , recArgOccurrences :: [Occurrence]
            , recAbstr          :: IsAbstract
            }
	  | Constructor
            { conPars   :: Nat         -- nof parameters
	    , conSrcCon :: QName       -- original constructor (this might be in a module instance)
	    , conData   :: QName       -- name of datatype
            , conHsCode :: Maybe (HaskellType, HaskellCode) -- used by the compiler
	    , conAbstr  :: IsAbstract
            , conInd    :: Induction   -- ^ Inductive or coinductive?
            }
	  | Primitive -- PrimFun
            { primAbstr :: IsAbstract
            , primName  :: String
            , primClauses :: [Clause]
            }
    deriving (Typeable, Data)

newtype Fields = Fields [(C.Name, Type)]
  deriving (Typeable, Data)

data Reduced no yes = NoReduction no | YesReduction yes
    deriving (Typeable)

data PrimFun = PrimFun
	{ primFunName		:: QName
	, primFunArity		:: Arity
	, primFunImplementation :: MonadTCM tcm => [Arg Term] -> tcm (Reduced [Arg Term] Term)
	}
    deriving (Typeable)

defClauses :: Definition -> [Clause]
defClauses Defn{theDef = Function{funClauses = cs}}	= cs
defClauses Defn{theDef = Primitive{primClauses = cs}}	= cs
defClauses Defn{theDef = Datatype{dataClause = Just c}} = [c]
defClauses Defn{theDef = Record{recClause = Just c}}    = [c]
defClauses _					        = []

-- | Used to specify whether something should be delayed.
data Delayed = Delayed | NotDelayed
  deriving (Typeable, Data, Show, Eq)

-- | Are the clauses of this definition delayed?
defDelayed :: Definition -> Delayed
defDelayed Defn{theDef = Function{funDelayed = d}} = d
defDelayed _                                       = NotDelayed

defAbstract :: Definition -> IsAbstract
defAbstract d = case theDef d of
    Axiom{}                   -> AbstractDef
    Function{funAbstr = a}    -> a
    Datatype{dataAbstr = a}   -> a
    Record{recAbstr = a}      -> a
    Constructor{conAbstr = a} -> a
    Primitive{primAbstr = a}  -> a


---------------------------------------------------------------------------
-- ** Injectivity
---------------------------------------------------------------------------

data FunctionInverse = NotInjective
                     | Inverse (Map TermHead Clause)
  deriving (Typeable, Data)

data TermHead = SortHead
              | PiHead
              | ConHead QName
  deriving (Typeable, Data, Eq, Ord, Show)

---------------------------------------------------------------------------
-- ** Mutual blocks
---------------------------------------------------------------------------

newtype MutualId = MutId Int
  deriving (Typeable, Data, Eq, Ord, Show, Num)

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
	  | forall a. CheckPattern A.Pattern Telescope Type (Maybe a)
	  | CheckLetBinding A.LetBinding (Maybe ())
	  | InferExpr A.Expr (Maybe (Term, Type))
	  | CheckExpr A.Expr Type (Maybe Term)
	  | CheckDotPattern A.Expr Term (Maybe ())
	  | CheckPatternShadowing A.Clause (Maybe ())
	  | IsTypeCall A.Expr Sort (Maybe Type)
	  | IsType_ A.Expr (Maybe Type)
	  | InferVar Name (Maybe (Term, Type))
	  | InferDef Range QName (Maybe (Term, Type))
	  | CheckArguments Range [NamedArg A.Expr] Type Type (Maybe (Args, Type, Constraints))
	  | CheckDataDef Range Name [A.LamBinding] [A.Constructor] (Maybe ())
	  | CheckRecDef Range Name [A.LamBinding] [A.Constructor] (Maybe ())
	  | CheckConstructor QName Telescope Sort A.Constructor (Maybe ())
	  | CheckFunDef Range Name [A.Clause] (Maybe ())
	  | CheckPragma Range A.Pragma (Maybe ())
	  | CheckPrimitive Range Name A.Expr (Maybe ())
          | CheckSectionApplication Range ModuleName A.Telescope ModuleName [NamedArg A.Expr] (Maybe ())
	  | ScopeCheckExpr C.Expr (Maybe A.Expr)
	  | ScopeCheckDeclaration D.NiceDeclaration (Maybe [A.Declaration])
	  | ScopeCheckLHS C.Name C.Pattern (Maybe A.LHS)
	  | ScopeCheckDefinition D.NiceDefinition (Maybe A.Definition)
	  | forall a. TermFunDef Range Name [A.Clause] (Maybe a)
	  | forall a. SetRange Range (Maybe a)	-- ^ used by 'setCurrentRange'
            -- actually, 'a' is Agda.Termination.TermCheck.CallGraph
            -- but I was to lazy to import the stuff here --Andreas,2007-5-29

    deriving (Typeable)

-- Dummy instance
instance Data Call where
  dataTypeOf _  = mkDataType "Call" []
  toConstr   x  = mkConstr (dataTypeOf x) "Dummy" [] Prefix
  gunfold k z _ = __IMPOSSIBLE__

instance HasRange a => HasRange (Trace a) where
    getRange (TopLevel _)      = noRange
    getRange (Current c par _ _)
      | r == noRange = getRange par
      | otherwise    = r
      where r = getRange c

instance HasRange a => HasRange (ParentCall a) where
  getRange NoParent = noRange
  getRange (Parent c par _)
    | r == noRange = getRange par
    | otherwise	   = r
    where r = getRange c

instance HasRange Call where
    getRange (CheckClause _ c _)                   = getRange c
    getRange (CheckPattern p _ _ _)                = getRange p
    getRange (InferExpr e _)                       = getRange e
    getRange (CheckExpr e _ _)                     = getRange e
    getRange (CheckLetBinding b _)                 = getRange b
    getRange (IsTypeCall e s _)                    = getRange e
    getRange (IsType_ e _)                         = getRange e
    getRange (InferVar x _)                        = getRange x
    getRange (InferDef _ f _)                      = getRange f
    getRange (CheckArguments r _ _ _ _)            = r
    getRange (CheckDataDef i _ _ _ _)              = getRange i
    getRange (CheckRecDef i _ _ _ _)               = getRange i
    getRange (CheckConstructor _ _ _ c _)          = getRange c
    getRange (CheckFunDef i _ _ _)                 = getRange i
    getRange (CheckPragma r _ _)                   = r
    getRange (CheckPrimitive i _ _ _)              = getRange i
    getRange (ScopeCheckExpr e _)                  = getRange e
    getRange (ScopeCheckDeclaration d _)           = getRange d
    getRange (ScopeCheckLHS _ p _)                 = getRange p
    getRange (ScopeCheckDefinition d _)            = getRange d
    getRange (CheckDotPattern e _ _)               = getRange e
    getRange (CheckPatternShadowing c _)           = getRange c
    getRange (TermFunDef i _ _ _)                  = getRange i
    getRange (SetRange r _)                        = r
    getRange (CheckSectionApplication r _ _ _ _ _) = r

---------------------------------------------------------------------------
-- ** Builtin things
---------------------------------------------------------------------------

type BuiltinThings pf = Map String (Builtin pf)

data Builtin pf
	= Builtin Term
	| Prim pf
    deriving (Typeable, Data)

instance Functor Builtin where
    fmap f (Builtin t) = Builtin t
    fmap f (Prim x)    = Prim $ f x

instance Foldable Builtin where
    foldr f z (Builtin t) = z
    foldr f z (Prim x)    = f x z

instance Traversable Builtin where
    traverse f (Builtin t) = pure $ Builtin t
    traverse f (Prim x)    = Prim <$> f x

---------------------------------------------------------------------------
-- * Type checking environment
---------------------------------------------------------------------------

data TCEnv =
    TCEnv { envContext             :: Context
	  , envLetBindings         :: LetBindings
	  , envCurrentModule       :: ModuleName
          , envAnonymousModules    :: [(ModuleName, Nat)] -- ^ anonymous modules and their number of free variables
	  , envImportPath          :: [C.TopLevelModuleName] -- ^ to detect import cycles
	  , envMutualBlock         :: Maybe MutualId -- ^ the current (if any) mutual block
	  , envAbstractMode        :: AbstractMode
		-- ^ When checking the typesignature of a public definition
		--   or the body of a non-abstract definition this is true.
		--   To prevent information about abstract things leaking
		--   outside the module.
          , envReplace             :: Bool
                -- ^ Coinductive constructor applications @c args@ get
                -- replaced by a function application @f tel@, where
                -- tel corresponds to the current telescope and @f@ is
                -- defined as @f tel = c args@. The initial occurrence
                -- of @c@ in the body of @f@ should not be replaced by
                -- yet another function application, though. To avoid
                -- that this happens the @envReplace@ flag is set to
                -- 'False' when @f@ is checked.
          , envDisplayFormsEnabled :: Bool
                -- ^ Sometimes we want to disable display forms.
          , envReifyInteractionPoints :: Bool
                -- ^ should we try to recover interaction points when reifying?
                --   disabled when generating types for with functions
	  }
    deriving (Typeable, Data)

initEnv :: TCEnv
initEnv = TCEnv { envContext	         = []
		, envLetBindings         = Map.empty
		, envCurrentModule       = noModuleName
                , envAnonymousModules    = []
		, envImportPath          = []
		, envMutualBlock         = Nothing
		, envAbstractMode        = AbstractMode
                , envReplace             = True
                , envDisplayFormsEnabled = True
                , envReifyInteractionPoints = True
		}

---------------------------------------------------------------------------
-- ** Context
---------------------------------------------------------------------------

type Context	  = [ContextEntry]
data ContextEntry = Ctx { ctxId	   :: CtxId
			, ctxEntry :: Arg (Name, Type)
			}
  deriving (Typeable, Data)

newtype CtxId	  = CtxId Nat
  deriving (Typeable, Data, Eq, Ord, Show, Enum, Real, Integral, Num)

---------------------------------------------------------------------------
-- ** Let bindings
---------------------------------------------------------------------------

type LetBindings = Map Name (Open (Term, Type))

---------------------------------------------------------------------------
-- ** Abstract mode
---------------------------------------------------------------------------

data AbstractMode = AbstractMode       -- ^ abstract things in the current module can be accessed
		  | ConcreteMode       -- ^ no abstract things can be accessed
		  | IgnoreAbstractMode -- ^ all abstract things can be accessed
  deriving (Typeable, Data)

---------------------------------------------------------------------------
-- * Type checking errors
---------------------------------------------------------------------------

-- Occurence of a name in a datatype definition
data Occ = OccCon { occDatatype	:: QName
	          , occConstructor :: QName
	          , occPosition	:: OccPos
	          }
         | OccClause { occFunction :: QName
                     , occClause   :: Int
                     , occPosition :: OccPos
                     }

data OccPos = NonPositively | ArgumentTo Nat QName

data TypeError
	= InternalError String
	| NotImplemented String
	| NotSupported String
        | CompilationError String
	| TerminationCheckFailed [([QName], [R.Range])]
          -- ^ Parameterised on functions which failed to termination
          --   check (grouped if they are mutual), along with ranges
          --   for problematic call sites.
	| PropMustBeSingleton
	| DataMustEndInSort Term
	| ShouldEndInApplicationOfTheDatatype Type
	    -- ^ The target of a constructor isn't an application of its
	    -- datatype. The 'Type' records what it does target.
	| ShouldBeAppliedToTheDatatypeParameters Term Term
	    -- ^ The target of a constructor isn't its datatype applied to
	    --	 something that isn't the parameters. First term is the correct
	    --	 target and the second term is the actual target.
	| ShouldBeApplicationOf Type QName
	    -- ^ Expected a type to be an application of a particular datatype.
	| ConstructorPatternInWrongDatatype QName QName -- ^ constructor, datatype
        | DoesNotConstructAnElementOf QName Term -- ^ constructor, type
	| DifferentArities
	    -- ^ Varying number of arguments for a function.
	| WrongHidingInLHS Type
	    -- ^ The left hand side of a function definition has a hidden argument
	    --	 where a non-hidden was expected.
	| WrongHidingInLambda Type
	    -- ^ Expected a non-hidden function and found a hidden lambda.
	| WrongHidingInApplication Type
	    -- ^ A function is applied to a hidden argument where a non-hidden was expected.
	| DependentPatternMatchingOnCodata
	| NotInductive Term
          -- ^ The term does not correspond to an inductive data type.
	| UninstantiatedDotPattern A.Expr
	| IlltypedPattern A.Pattern Type
	| TooManyArgumentsInLHS Nat Type
	| WrongNumberOfConstructorArguments QName Nat Nat
	| ShouldBeEmpty Type [Pattern]
	| ShouldBeASort Type
	    -- ^ The given type should have been a sort.
	| ShouldBePi Type
	    -- ^ The given type should have been a pi.
	| ShouldBeRecordType Type
	| NotAProperTerm
	| UnequalTerms Comparison Term Term Type
	| UnequalTypes Comparison Type Type
	| UnequalTelescopes Comparison Telescope Telescope
	| UnequalHiding Type Type
	    -- ^ The two function types have different hiding.
	| UnequalSorts Sort Sort
	| NotLeqSort Sort Sort
	| MetaCannotDependOn MetaId [Nat] Nat
	    -- ^ The arguments are the meta variable, the parameters it can
	    --	 depend on and the paratemeter that it wants to depend on.
	| MetaOccursInItself MetaId
	| GenericError String
        | BuiltinMustBeConstructor String A.Expr
	| NoSuchBuiltinName String
	| DuplicateBuiltinBinding String Term Term
	| NoBindingForBuiltin String
	| NoSuchPrimitiveFunction String
        | ShadowedModule [A.ModuleName]
	| BuiltinInParameterisedModule String
	| NoRHSRequiresAbsurdPattern [NamedArg A.Pattern]
	| AbsurdPatternRequiresNoRHS [NamedArg A.Pattern]
	| TooFewFields QName [C.Name]
	| TooManyFields QName [C.Name]
	| DuplicateFields [C.Name]
	| DuplicateConstructors [C.Name]
	| UnexpectedWithPatterns [A.Pattern]
	| WithClausePatternMismatch A.Pattern Pattern
        | FieldOutsideRecord
        | ModuleArityMismatch A.ModuleName Telescope [NamedArg A.Expr]
    -- Coverage errors
	| IncompletePatternMatching Term Args -- can only happen if coverage checking is switched off
        | CoverageFailure QName [[Arg Pattern]]
        | UnreachableClauses QName [[Arg Pattern]]
        | CoverageCantSplitOn QName
        | CoverageCantSplitType Type
    -- Positivity errors
	| NotStrictlyPositive QName [Occ]
    -- Import errors
	| LocalVsImportedModuleClash ModuleName
	| UnsolvedMetas [Range]
	| UnsolvedConstraints Constraints
	| CyclicModuleDependency [C.TopLevelModuleName]
	| FileNotFound C.TopLevelModuleName [FilePath]
	| ModuleNameDoesntMatchFileName C.TopLevelModuleName [FilePath]
	| ClashingFileNamesFor ModuleName [FilePath]
        | ModuleDefinedInOtherFile C.TopLevelModuleName FilePath FilePath
          -- ^ Module name, file from which it was loaded, file which
          -- the include path says contains the module.
    -- Scope errors
	| BothWithAndRHS
	| NotInScope [C.QName]
	| NoSuchModule C.QName
	| AmbiguousName C.QName [A.QName]
	| AmbiguousModule C.QName [A.ModuleName]
	| UninstantiatedModule C.QName
	| ClashingDefinition C.QName A.QName
	| ClashingModule A.ModuleName A.ModuleName
	| ClashingImport C.Name A.QName
	| ClashingModuleImport C.Name A.ModuleName
	| PatternShadowsConstructor A.Name A.QName
	| ModuleDoesntExport C.QName [C.ImportedName]
	| InvalidPattern C.Pattern
	| RepeatedVariablesInPattern [C.Name]
    -- Concrete to Abstract errors
	| NotAModuleExpr C.Expr
	    -- ^ The expr was used in the right hand side of an implicit module
	    --	 definition, but it wasn't of the form @m Delta@.
	| NotAnExpression C.Expr
	| NotAValidLetBinding D.NiceDeclaration
	| NothingAppliedToHiddenArg C.Expr
    -- Operator errors
	| NoParseForApplication [C.Expr]
	| AmbiguousParseForApplication [C.Expr] [C.Expr]
	| NoParseForLHS C.Pattern
	| AmbiguousParseForLHS C.Pattern [C.Pattern]
    -- Usage errors
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
-- * Type checking monad transformer
---------------------------------------------------------------------------

newtype TCMT m a = TCM { unTCM :: UndoT TCState
			          (StateT TCState
			          (ReaderT TCEnv
			          (ErrorT TCErr m))) a
		       }
    deriving ( MonadState TCState
             , MonadReader TCEnv
             , MonadError TCErr
             , MonadUndo TCState
             )

type TCM = TCMT IO

class ( Applicative tcm, MonadIO tcm
      , MonadReader TCEnv tcm
      , MonadState TCState tcm
      ) => MonadTCM tcm where
    liftTCM :: TCM a -> tcm a

mapTCMT :: (m (Either TCErr ((a, [TCState]), TCState)) ->
            n (Either TCErr ((b, [TCState]), TCState))
           ) -> TCMT m a -> TCMT n b
mapTCMT f = TCM . mapUndoT (mapStateT (mapReaderT (mapErrorT f))) . unTCM

instance MonadIO m => MonadTCM (TCMT m) where
    liftTCM = mapTCMT liftIO

instance MonadTrans TCMT where
    lift = TCM . lift . lift . lift . lift

-- We want a special monad implementation of fail.
instance MonadIO m => Monad (TCMT m) where
    return  = TCM . return
    m >>= k = TCM $ unTCM m >>= unTCM . k
    fail    = internalError

instance MonadIO m => Functor (TCMT m) where
    fmap = liftM

instance MonadIO m => Applicative (TCMT m) where
    pure = return
    (<*>) = ap

instance MonadIO m => MonadIO (TCMT m) where
  liftIO m = TCM $ do tr <- gets stTrace
                      lift $ lift $ lift $ ErrorT $ liftIO $
                        handle (handleIOException $ getRange tr)
                        (failOnException
                         (\r -> return . throwError . Exception r)
                         (return <$> m) )
    where
      handleIOException r e = case e of
        IOException _ -> return . throwError . Exception r . show $ e
        _             -> throwIO e

patternViolation :: MonadTCM tcm => tcm a
patternViolation = liftTCM $ do
    s <- get
    throwError $ PatternErr s

internalError :: MonadTCM tcm => String -> tcm a
internalError s = typeError $ InternalError s

typeError :: MonadTCM tcm => TypeError -> tcm a
typeError err = liftTCM $ do
    cl <- buildClosure err
    s  <- get
    throwError $ TypeError s cl

handleTypeErrorException :: MonadTCM tcm => IO a -> tcm a
handleTypeErrorException m = do
    r <- liftIO $ liftM Right m `catchDyn` (return . Left)
    either typeError return r

-- | Running the type checking monad
runTCM :: Monad m => TCMT m a -> m (Either TCErr a)
runTCM m = runErrorT
	 $ flip runReaderT initEnv
	 $ flip evalStateT initState
	 $ runUndoT
	 $ unTCM m

