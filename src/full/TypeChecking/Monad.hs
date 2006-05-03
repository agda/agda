{-# OPTIONS -fglasgow-exts #-}
module TypeChecking.Monad where

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
    TCSt { stNextMeta	    :: MetaId
	 , stNextName	    :: NameId
	 , stNextConstraint :: ConstraintId
	 , stMetaStore	    :: MetaStore
	 , stConstraints    :: Constraints
	 , stSignature	    :: Signature
	 }

instance HasFresh MetaId TCState where
    nextFresh s = (i, s { stNextMeta = i + 1 })
	where
	    i = stNextMeta s

instance HasFresh NameId TCState where
    nextFresh s = (i, s { stNextName = i + 1 })
	where
	    i = stNextName s

instance HasFresh ConstraintId TCState where
    nextFresh s = (i, s { stNextConstraint = i + 1 })
	where
	    i = stNextConstraint s

---------------------------------------------------------------------------
-- ** Constraints
---------------------------------------------------------------------------

newtype ConstraintId = CId Nat
    deriving (Eq, Ord, Show, Num, Typeable, Data)

data Constraint = ValueEq Type Value Value
		| TypeEq Type Type
  deriving Show

type Constraints = [(ConstraintId,(Signature,Context,Constraint))]

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

type MetaStore = [(MetaId, MetaVariable)]

---------------------------------------------------------------------------
-- * Type checking environment
---------------------------------------------------------------------------

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

type TCErrMon = Either TCErr
type TCM a = StateT TCState (ReaderT Context TCErrMon) a

--
-- Context and Signature
--
type Context = [CtxElm]
type Signature = Context

data CtxElm = Decl Name Type (Maybe [Name]) -- ^ ind. types have list of constructors
	    | Defn Name [Clause]
	    | NameSpace Name Context
  deriving (Typeable, Data, Show)

-- | get globally new symbol (@Int@)
--
genSym :: TCM MetaId
genSym = fresh

