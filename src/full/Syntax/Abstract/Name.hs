{-# OPTIONS -fglasgow-exts -cpp #-}

{-| Abstract names should carry unique identifiers and stuff. Not right now though.
-}
module Syntax.Abstract.Name where

import Control.Monad.State
import Data.Generics (Typeable, Data)

import Syntax.Position
import Syntax.Common
import qualified Syntax.Concrete.Name as C

import Utils.Fresh

#include "../../undefined.h"

-- | The unique identifier of a name.
newtype NameId = NameId Nat
    deriving (Eq, Ord, Num, Typeable, Data)

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

qualifyModuleHack :: Maybe ModuleName -> ModuleName -> ModuleName
qualifyModuleHack (Just m) (MName (C.QName x) _) = qualifyModule m x
qualifyModuleHack Nothing  m' = m'
qualifyModuleHack _ _ = __IMPOSSIBLE__

isSubModuleOf :: ModuleName -> ModuleName -> Bool
isSubModuleOf x y = isSub (mnameId x) (mnameId y)
    where
	isSub (C.QName x)  (C.QName z)	= x == z
	isSub (C.Qual x y) (C.QName z)	= x == z
	isSub (C.Qual x y) (C.Qual z w) = x == z && isSub y w
	isSub (C.QName _)  (C.Qual _ _) = False

freshName :: (MonadState s m, HasFresh NameId s) => Range -> String -> m Name
freshName r s =
    do	i <- fresh
	return $ Name i (C.Name r s)

freshName_ :: (MonadState s m, HasFresh NameId s) => String -> m Name
freshName_ = freshName noRange

freshNoName :: (MonadState s m, HasFresh NameId s) => Range -> m Name
freshNoName r =
    do	i <- fresh
	return $ Name i (C.NoName r)

freshNoName_ :: (MonadState s m, HasFresh NameId s) => m Name
freshNoName_ = freshNoName noRange

instance Show NameId where
    show (NameId x) = show x

instance Eq Name where
    x == y  = nameId x == nameId y

instance Ord Name where
    compare x y = compare (nameId x) (nameId y)

instance Show Name where
    show x = show (nameConcrete x)

instance Show QName where
    show q = {-show (qnameModule q) ++ "." ++-} show (qnameName q)

instance Eq QName where
    x == y = (qnameModule x, qnameName x) == (qnameModule y, qnameName y)

instance Ord QName where
    compare x y = compare (qnameModule x, qnameName x) (qnameModule y, qnameName y)

instance Show ModuleName where
    show m = show (mnameConcrete m)

instance Eq ModuleName where
    m1 == m2 = mnameId m1 == mnameId m2

instance Ord ModuleName where
    compare m1 m2 = compare (mnameId m1) (mnameId m2)

instance HasRange Name where
    getRange = getRange . nameConcrete

instance HasRange QName where
    getRange = getRange . qnameConcrete

instance HasRange ModuleName where
    getRange = getRange . mnameConcrete


