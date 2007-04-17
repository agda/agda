{-# OPTIONS -fglasgow-exts -cpp #-}

{-| Abstract names should carry unique identifiers and stuff. Not right now though.
-}
module Syntax.Abstract.Name where

import Control.Monad.State
import Data.Generics (Typeable, Data)
import Data.List

import Syntax.Position
import Syntax.Common
import Syntax.Fixity
import qualified Syntax.Concrete.Name as C

import Utils.Fresh
import Utils.Function
import Utils.Size

#include "../../undefined.h"

-- | The unique identifier of a name.
newtype NameId = NameId Nat
    deriving (Eq, Ord, Num, Typeable, Data)

-- | A name is a unique identifier and a suggestion for a concrete name. The
--   concrete name contains the source location (if any) of the name. The
--   source location of the binding site is also recorded.
data Name = Name { nameId	   :: NameId
		 , nameConcrete	   :: C.Name
		 , nameBindingSite :: Range
		 , nameFixity	   :: Fixity
		 }
    deriving (Typeable, Data)

-- | Qualified names are non-empty lists of names. Equality on qualified names
--   are just equality on the last name, i.e. the module part is just for show.
data QName = QName { qnameModule :: [Name]
		   , qnameName	 :: Name
		   }
    deriving (Typeable, Data)

-- | A module name is just a qualified name.
type ModuleName = QName

invisibleTopModuleName :: Name
invisibleTopModuleName = Name (-1) (C.noName noRange) noRange defaultFixity

mkName_ :: NameId -> String -> Name
mkName_ = mkName noRange

mkName :: Range -> NameId -> String -> Name
mkName r i s = Name i (C.Name r (parseName s)) r defaultFixity
  where
    parseName ""      = []
    parseName ('_':s) = C.Hole : parseName s
    parseName s = case break (== '_') s of
      (s0, s1)	-> C.Id s0 : parseName s1

qnameToList :: QName -> [Name]
qnameToList (QName xs x) = xs ++ [x]

qnameFromList :: [Name] -> QName
qnameFromList [] = __IMPOSSIBLE__
qnameFromList xs = QName (init xs) (last xs)

-- | Turn a qualified name into a concrete name. This should only be used as a
--   fallback when looking up the right concrete name in the scope fails.
qnameToConcrete :: QName -> C.QName
qnameToConcrete (QName m x) =
  foldr C.Qual (C.QName $ nameConcrete x) $ map nameConcrete m

qualifyQ :: ModuleName -> QName -> QName
qualifyQ m x = qnameFromList $ qnameToList m ++ qnameToList x

qualify :: ModuleName -> Name -> QName
qualify m x = qualifyQ m (qnameFromList [x])

isSubModuleOf :: ModuleName -> ModuleName -> Bool
isSubModuleOf x y = xs /= ys && isPrefixOf ys xs
  where
    xs = qnameToList x
    ys = qnameToList y

freshName :: (MonadState s m, HasFresh NameId s) => Range -> String -> m Name
freshName r s = do
  i <- fresh
  return $ mkName r i s

freshName_ :: (MonadState s m, HasFresh NameId s) => String -> m Name
freshName_ = freshName noRange

freshNoName :: (MonadState s m, HasFresh NameId s) => Range -> m Name
freshNoName r =
    do	i <- fresh
	return $ Name i (C.noName r) r defaultFixity

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
    show q = concat $ intersperse "." $ map show $ qnameToList q

instance Eq QName where
    (==) = (==) `on` qnameName

instance Ord QName where
    compare = compare `on` qnameName

instance HasRange Name where
    getRange = getRange . nameConcrete

instance HasRange QName where
    getRange = getRange . qnameName

instance SetRange Name where
  setRange r x = x { nameConcrete = setRange r $ nameConcrete x }

instance SetRange QName where
  setRange r q = q { qnameName = setRange r $ qnameName q }

instance Sized QName where
  size = size . qnameToList

