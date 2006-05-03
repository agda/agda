{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}
module TypeChecking.Monad where

import Data.Map as Map

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Reader
import Data.Generics

import Syntax.Common
import Syntax.Internal
import Syntax.Internal.Debug ()

import Utils.Fresh

---------------------------------------------------------------------------
-- * Type checking state
---------------------------------------------------------------------------

data TCState =
    TCSt { stFreshThings    :: FreshThings
	 , stMetaStore	    :: MetaStore
	 , stConstraints    :: Constraints
	 , stSignature	    :: Signature
	 }

data FreshThings =
	Fresh { fMeta	    :: MetaId
	      , fName	    :: NameId
	      , fConstraint :: ConstraintId
	      }
    deriving (Show)

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

data Constraint = ValueEq Type Value Value
		| TypeEq Type Type
  deriving Show

type Constraints = Map ConstraintId (Signature,Context,Constraint)

---------------------------------------------------------------------------
-- ** Meta variables
---------------------------------------------------------------------------

data MetaVariable = InstV Value
                  | InstT Type
                  | InstS Sort
                  | UnderScoreV Type [ConstraintId]
                  | UnderScoreT Sort [ConstraintId]
                  | UnderScoreS      [ConstraintId]
                  | HoleV       Type [ConstraintId]
                  | HoleT       Sort [ConstraintId]
  deriving (Typeable, Data, Show)

type MetaStore = Map MetaId MetaVariable

---------------------------------------------------------------------------
-- ** Signature
---------------------------------------------------------------------------

type Signature = Map QName Definition

data Definition = Axiom	      { defType    :: Type			      }
		| Function    { funClauses :: [Clause], defType     :: Type   }
		| Datatype    { defType    :: Type    , dataConstrs :: [Name] }
		| Constructor { defType    :: Type    , conDatatype :: Name   }
		    -- ^ The type of the constructor and the name of the datatype.
    deriving (Show)

defClauses :: Definition -> [Clause]
defClauses (Function cs _) = cs
defClauses _		   = []

---------------------------------------------------------------------------
-- * Type checking environment
---------------------------------------------------------------------------

data TCEnv =
    TCEnv { envContext :: Context
	  }

---------------------------------------------------------------------------
-- ** Context
---------------------------------------------------------------------------

type Context = [(Name, Type)]

---------------------------------------------------------------------------
-- * Type checking errors
---------------------------------------------------------------------------

data TCErr = Fatal String 
	   | PatternErr MetaId -- ^ for pattern violations, carries involved metavar
  deriving Show

instance Error TCErr where
    noMsg = Fatal ""
    strMsg s = Fatal s

patternViolation mId = throwError $ PatternErr mId

---------------------------------------------------------------------------
-- * Type checking monad
---------------------------------------------------------------------------

type TCErrMon = Either TCErr
type TCM a = StateT TCState (ReaderT TCEnv TCErrMon) a

