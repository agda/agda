{-# OPTIONS -fglasgow-exts #-}
module TypeChecking.Monad where

import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Reader
import Data.Generics

import Syntax.Internal
import Syntax.Internal.Debug ()

import Utils.Fresh

--
-- Monad
--
data TCState = TCSt {
  genSymSt :: Int,	-- ^ shared between meta ids and name ids (should be split up)
  metaSt   :: Store,
  cnstrSt  :: Constraints,
  sigSt    :: Signature
}

instance HasFresh Int TCState where
    nextFresh s = (i, s { genSymSt = i + 1 })
	where
	    i = genSymSt s

instance Show TCState where 
    show st = 
        "{genSymSt="++(show $ genSymSt st)++
        ", metaSt="++(show $ map StoreElm $ metaSt st)++
        ", cnstrSt="++(show $ cnstrSt st)++
        ", sigSt="++(show $ sigSt st)++
        "}"

newtype StoreElm = StoreElm (MId, MetaVariable)
instance Show StoreElm where show (StoreElm x) = storeElm2str x
storeElm2str (x, mv) = "?"++(show x)++(case mv of
    InstV v -> ":="++(show v)
    InstT a -> ":="++(show a)
    InstS s -> ":="++(show s)
    UnderScoreV a cIds -> ":"++(show a)++"|"++(show cIds)
    UnderScoreT s cIds -> ":"++(show s)++"|"++(show cIds)
    UnderScoreS cIds -> "|"++(show cIds)
    HoleV a cIds -> ":"++(show a)++"|"++(show cIds)
    HoleT s cIds -> ":"++(show s)++"|"++(show cIds)
  )

-- | Type Checking errors
--
data TCErr = Fatal String 
	   | PatternErr MId -- ^ for pattern violations, carries involved metavar
  deriving Show

instance Error TCErr where
    noMsg = Fatal ""
    strMsg s = Fatal s
patternViolation mId = throwError $ PatternErr mId

type TCErrMon = Either TCErr
type TCM a = StateT TCState (ReaderT Context TCErrMon) a

--
-- Constraints
--
type ConstraintId = Int

data Constraint = ValueEq Type Value Value
		| TypeEq Type Type
  deriving Show

type Constraints = [(ConstraintId,(Signature,Context,Constraint))]

--
-- Meta Variables
--
data MetaVariable = InstV Value
                  | InstT Type
                  | InstS Sort
                  | UnderScoreV Type [ConstraintId]
                  | UnderScoreT Sort [ConstraintId]
                  | UnderScoreS      [ConstraintId]
                  | HoleV       Type [ConstraintId]
                  | HoleT       Sort [ConstraintId]
  deriving (Typeable, Data, Show)

type Store = [(MId, MetaVariable)]

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
genSym :: TCM Int
genSym = fresh

