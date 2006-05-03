{-# OPTIONS -fglasgow-exts #-}

{-| Abstract names should carry unique identifiers and stuff. Not right now though.
-}
module Syntax.Abstract.Name where

import Control.Monad.State
import Data.Generics (Typeable, Data)

import Syntax.Position
import Syntax.Common
import qualified Syntax.Concrete.Name as C

import Utils.Fresh

-- | The unique identifier of a name.
type NameId = Nat

-- | Modules are (temporarily) identified by their concrete names.
type ModuleId = C.QName

data Name = Name { nameId       :: NameId
		 , nameConcrete :: C.Name
		 }
    deriving (Typeable, Data)

data QName = QName { qnameName	   :: Name
		   , qnameModule   :: ModuleName
		   , qnameConcrete :: C.QName
		   }
    deriving (Typeable, Data)

data ModuleName =
    MName { mnameId	  :: ModuleId
	  , mnameConcrete :: C.QName
	  }
    deriving (Typeable, Data)

mkName :: NameId -> String -> Name
mkName i s = Name i (C.Name noRange s)

mkModuleName :: C.QName -> ModuleName
mkModuleName x = MName x x

qualify :: ModuleName -> Name -> QName
qualify m x = QName { qnameName	    = x
		    , qnameModule   = m
		    , qnameConcrete = C.qualify (mnameConcrete m) (nameConcrete x)
		    }

qualifyModule :: ModuleName -> C.Name -> ModuleName
qualifyModule (MName i c) x = MName (C.qualify i x) (C.qualify c x)

freshName :: (MonadState s m, HasFresh NameId s) => Range -> String -> m Name
freshName r s =
    do	i <- fresh
	return $ Name i (C.Name r s)

freshName_ :: (MonadState s m, HasFresh NameId s) => String -> m Name
freshName_ = freshName noRange

instance Eq Name where
    x == y  = nameId x == nameId y

instance Ord Name where
    compare x y = compare (nameId x) (nameId y)

instance Show Name where
    show = show . nameConcrete

instance Show QName where
    show q = show (qnameModule q) ++ "." ++ show (qnameConcrete q)

instance Eq QName where
    x == y = qnameModule x == qnameModule y && qnameName x == qnameName y

instance Show ModuleName where
    show m = show (mnameConcrete m)

instance Eq ModuleName where
    m1 == m2 = mnameId m1 == mnameId m2

instance HasRange Name where
    getRange = getRange . nameConcrete

instance HasRange QName where
    getRange = getRange . qnameConcrete

instance HasRange ModuleName where
    getRange = getRange . mnameConcrete


