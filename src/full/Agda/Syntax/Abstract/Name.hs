{-# LANGUAGE CPP, DeriveDataTypeable, GeneralizedNewtypeDeriving, FlexibleContexts #-}

{-| Abstract names should carry unique identifiers and stuff. Not right now though.
-}
module Agda.Syntax.Abstract.Name where

import Control.Monad.State
import Data.Generics (Typeable, Data)
import Data.List
import Data.Function

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import qualified Agda.Syntax.Concrete.Name as C

import Agda.Utils.Fresh
import Agda.Utils.Size
import Agda.Utils.Suffix

#include "../../undefined.h"
import Agda.Utils.Impossible

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
data QName = QName { qnameModule :: ModuleName
		   , qnameName	 :: Name
		   }
    deriving (Typeable, Data)

-- | A module name is just a qualified name.
newtype ModuleName = MName { mnameToList :: [Name] }
  deriving (Eq, Ord, Typeable, Data)

-- | Ambiguous qualified names. Used for overloaded constructors.
--
-- Invariant: All the names in the list must have the same concrete,
-- unqualified name.
newtype AmbiguousQName = AmbQ { unAmbQ :: [QName] }
  deriving (Typeable, Data, HasRange)

instance HasRange ModuleName where
  getRange (MName []) = noRange
  getRange (MName xs) = getRange $ last xs

mnameFromList :: [Name] -> ModuleName
mnameFromList = MName

noModuleName :: ModuleName
noModuleName = mnameFromList []

-- | The 'Range' sets the /definition site/ of the name, not the use
-- site.

mkName :: Range -> NameId -> String -> Name
mkName r i s = Name i (C.Name noRange (parseName s)) r defaultFixity
  where
    parseName ""      = []
    parseName ('_':s) = C.Hole : parseName s
    parseName s = case break (== '_') s of
      (s0, s1)	-> C.Id s0 : parseName s1

mkName_ :: NameId -> String -> Name
mkName_ = mkName noRange

qnameToList :: QName -> [Name]
qnameToList (QName m x) = mnameToList m ++ [x]

qnameFromList :: [Name] -> QName
qnameFromList [] = __IMPOSSIBLE__
qnameFromList xs = QName (mnameFromList $ init xs) (last xs)

-- | Turn a qualified name into a concrete name. This should only be used as a
--   fallback when looking up the right concrete name in the scope fails.
qnameToConcrete :: QName -> C.QName
qnameToConcrete (QName m x) =
  foldr C.Qual (C.QName $ nameConcrete x) $ map nameConcrete $ mnameToList m

mnameToConcrete :: ModuleName -> C.QName
mnameToConcrete (MName []) = __IMPOSSIBLE__ -- C.QName C.noName_  -- should never happen?
mnameToConcrete (MName xs) = foldr C.Qual (C.QName $ last cs) $ init cs
  where
    cs = map nameConcrete xs

qualifyM :: ModuleName -> ModuleName -> ModuleName
qualifyM m1 m2 = mnameFromList $ mnameToList m1 ++ mnameToList m2

qualifyQ :: ModuleName -> QName -> QName
qualifyQ m x = qnameFromList $ mnameToList m ++ qnameToList x

qualify :: ModuleName -> Name -> QName
qualify m x = qualifyQ m (qnameFromList [x])

-- | Is the name an operator?

isOperator :: QName -> Bool
isOperator q = C.isOperator (nameConcrete (qnameName q))

isSubModuleOf :: ModuleName -> ModuleName -> Bool
isSubModuleOf x y = xs /= ys && isPrefixOf ys xs
  where
    xs = mnameToList x
    ys = mnameToList y

isInModule :: QName -> ModuleName -> Bool
isInModule q m = mnameToList m `isPrefixOf` qnameToList q

freshName :: (MonadState s m, HasFresh NameId s) => Range -> String -> m Name
freshName r s = do
  i <- fresh
  return $ mkName r i s

freshName_ :: (MonadState s m, HasFresh NameId s) => String -> m Name
freshName_ = freshName noRange

freshNoName :: (MonadState s m, HasFresh NameId s) => Range -> m Name
freshNoName r =
    do	i <- fresh
	return $ Name i (C.NoName noRange i) r defaultFixity

freshNoName_ :: (MonadState s m, HasFresh NameId s) => m Name
freshNoName_ = freshNoName noRange

-- | Get the next version of the concrete name. For instance, @nextName "x" = "x'"@.
--   The name must not be a 'NoName'.
nextName :: Name -> Name
nextName x = x { nameConcrete = C.Name noRange $ nextSuf ps }
    where
	C.Name _ ps = nameConcrete x
	-- NoName cannot appear here
	nextSuf [C.Id s]         = [C.Id $ nextStr s]
	nextSuf [C.Id s, C.Hole] = [C.Id $ nextStr s, C.Hole]
	nextSuf (p : ps)         = p : nextSuf ps
	nextSuf []               = __IMPOSSIBLE__
	nextStr s = case suffixView s of
	    (s0, suf) -> addSuffix s0 (nextSuffix suf)

instance Show NameId where
  show (NameId x i) = show x ++ "@" ++ show i

instance Eq Name where
  x == y  = nameId x == nameId y

instance Ord Name where
  compare x y = compare (nameId x) (nameId y)

instance Show Name where
  show x = show (nameConcrete x) -- ++ "|" ++ show (nameId x)

instance Show QName where
  show q = concat $ intersperse "." $ map show $ qnameToList q

instance Show ModuleName where
  show m = concat $ intersperse "." $ map show $ mnameToList m

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

instance KillRange QName where
  killRange q = q { qnameName = killRange $ qnameName q }

instance KillRange Name where
  killRange x = x { nameConcrete = killRange $ nameConcrete x }

instance KillRange ModuleName where
  killRange (MName xs) = MName $ killRange xs

instance KillRange AmbiguousQName where
  killRange (AmbQ xs) = AmbQ $ killRange xs

instance Sized QName where
  size = size . qnameToList

instance Sized ModuleName where
  size = size . mnameToList

