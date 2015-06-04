{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| Abstract names carry unique identifiers and stuff.
-}
module Agda.Syntax.Abstract.Name
  ( module Agda.Syntax.Abstract.Name
  , IsNoName(..)
  ) where

import Control.Monad.State

import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
import Data.Typeable (Typeable)
import Data.List
import Data.Function
import Data.Hashable

import GHC.Generics (Generic)

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import Agda.Syntax.Concrete.Name (IsNoName(..))
import qualified Agda.Syntax.Concrete.Name as C

-- import Agda.Utils.Function
import Agda.Utils.Pretty
import Agda.Utils.Size
import Agda.Utils.Suffix

#include "undefined.h"
import Agda.Utils.Impossible

-- | A name is a unique identifier and a suggestion for a concrete name. The
--   concrete name contains the source location (if any) of the name. The
--   source location of the binding site is also recorded.
data Name = Name { nameId          :: NameId
                 , nameConcrete    :: C.Name
                 , nameBindingSite :: Range
                 , nameFixity      :: Fixity'
                 }
    deriving (Typeable, Generic)

-- | Qualified names are non-empty lists of names. Equality on qualified names
--   are just equality on the last name, i.e. the module part is just
--   for show.
--
-- The 'SetRange' instance for qualified names sets all individual
-- ranges (including those of the module prefix) to the given one.
data QName = QName { qnameModule :: ModuleName
                   , qnameName   :: Name
                   }
    deriving (Typeable, Generic)

-- | Something preceeded by a qualified name.
data QNamed a = QNamed
  { qname  :: QName
  , qnamed :: a
  }
  deriving (Typeable, Generic, Show, Functor, Foldable, Traversable)

-- | A module name is just a qualified name.
--
-- The 'SetRange' instance for module names sets all individual ranges
-- to the given one.
newtype ModuleName = MName { mnameToList :: [Name] }
  deriving (Eq, Ord, Typeable, Generic)

-- | Ambiguous qualified names. Used for overloaded constructors.
--
-- Invariant: All the names in the list must have the same concrete,
-- unqualified name.  (This implies that they all have the same 'Range').
newtype AmbiguousQName = AmbQ { unAmbQ :: [QName] }
  deriving (Typeable, Generic, Show)

-- | A module is anonymous if the qualification path ends in an underscore.
isAnonymousModuleName :: ModuleName -> Bool
isAnonymousModuleName (MName []) = False
isAnonymousModuleName (MName ms) = isNoName $ last ms

-- | Sets the ranges of the individual names in the module name to
-- match those of the corresponding concrete names. If the concrete
-- names are fewer than the number of module name name parts, then the
-- initial name parts get the range 'noRange'.
--
-- @C.D.E \`withRangesOf\` [A, B]@ returns @C.D.E@ but with ranges set
-- as follows:
--
-- * @C@: 'noRange'.
--
-- * @D@: the range of @A@.
--
-- * @E@: the range of @B@.
--
-- Precondition: The number of module name name parts has to be at
-- least as large as the length of the list.

withRangesOf :: ModuleName -> [C.Name] -> ModuleName
MName ms `withRangesOf` ns
  | length ms < length ns  = __IMPOSSIBLE__
  | otherwise              = MName $
      reverse $ zipWith setRange
                        (reverse (map getRange ns) ++ repeat noRange)
                        (reverse ms)

-- | Like 'withRangesOf', but uses the name parts (qualifier + name)
-- of the qualified name as the list of concrete names.

withRangesOfQ :: ModuleName -> C.QName -> ModuleName
m `withRangesOfQ` q = m `withRangesOf` C.qnameParts q

mnameFromList :: [Name] -> ModuleName
mnameFromList = MName

noModuleName :: ModuleName
noModuleName = mnameFromList []

-- | Make a 'Name' from some kind of string.
class MkName a where
  -- | The 'Range' sets the /definition site/ of the name, not the use site.
  mkName :: Range -> NameId -> a -> Name

  mkName_ :: NameId -> a -> Name
  mkName_ = mkName noRange

instance MkName String where
  mkName r i s = Name i (C.Name noRange (C.stringNameParts s)) r defaultFixity'


qnameToList :: QName -> [Name]
qnameToList (QName m x) = mnameToList m ++ [x]

qnameFromList :: [Name] -> QName
qnameFromList [] = __IMPOSSIBLE__
qnameFromList xs = QName (mnameFromList $ init xs) (last xs)

qnameToMName :: QName -> ModuleName
qnameToMName = mnameFromList . qnameToList

mnameToQName :: ModuleName -> QName
mnameToQName = qnameFromList . mnameToList

showQNameId :: QName -> String
showQNameId q = show ns ++ "@" ++ show m
  where
    is = map nameId $ mnameToList (qnameModule q) ++ [qnameName q]
    ns = [ n | NameId n _ <- is ]
    m  = head [ m | NameId _ m <- is ]

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

-- | Computes the 'TopLevelModuleName' corresponding to the given
-- module name, which is assumed to represent a top-level module name.
--
-- Precondition: The module name must be well-formed.

toTopLevelModuleName :: ModuleName -> C.TopLevelModuleName
toTopLevelModuleName (MName []) = __IMPOSSIBLE__
toTopLevelModuleName (MName ms) = C.TopLevelModuleName $ map (C.nameToRawName . nameConcrete) ms

qualifyM :: ModuleName -> ModuleName -> ModuleName
qualifyM m1 m2 = mnameFromList $ mnameToList m1 ++ mnameToList m2

qualifyQ :: ModuleName -> QName -> QName
qualifyQ m x = qnameFromList $ mnameToList m ++ qnameToList x

qualify :: ModuleName -> Name -> QName
qualify = QName

-- | Convert a 'Name' to a 'QName' (add no module name).
qualify_ :: Name -> QName
qualify_ = qualify noModuleName

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

-- | Get the next version of the concrete name. For instance, @nextName "x" = "x₁"@.
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

------------------------------------------------------------------------
-- * Important instances: Eq, Ord, Hashable
--
--   For the identity and comparing of names, only the 'NameId' matters!
------------------------------------------------------------------------

instance Eq Name where
  (==) = (==) `on` nameId

instance Ord Name where
  compare = compare `on` nameId

instance Hashable Name where
  {-# INLINE hashWithSalt #-}
  hashWithSalt salt = hashWithSalt salt . nameId

instance Eq QName where
  (==) = (==) `on` qnameName

instance Ord QName where
  compare = compare `on` qnameName

instance Hashable QName where
  {-# INLINE hashWithSalt #-}
  hashWithSalt salt = hashWithSalt salt . qnameName

------------------------------------------------------------------------
-- * IsNoName instances (checking for "_")
------------------------------------------------------------------------

-- | An abstract name is empty if its concrete name is empty.
instance IsNoName Name where
  isNoName = isNoName . nameConcrete

------------------------------------------------------------------------
-- * Show instances
------------------------------------------------------------------------

-- | Only use this @show@ function in debugging!  To convert an
--   abstract 'Name' into a string use @prettyShow@.
instance Show Name where
  -- Andreas, 2014-10-02: Reverted to nice printing.
  -- Reason: I do not have time just now to properly fix the
  -- use of Show Name for pretty printing everywhere, e.g. in
  -- the Epic backend.  But I want to push the fix for Issue 836 now.
  show n = show (nameConcrete n)
  -- show n = show (nameConcrete n) ++ "^" ++ show (nameId n)
  -- show n = applyWhen (isNoName n) (++ show (nameId n)) $ show (nameConcrete n)

-- | Only use this @show@ function in debugging!  To convert an
--   abstract 'ModuleName' into a string use @prettyShow@.
instance Show ModuleName where
  show m = concat $ intersperse "." $ map show $ mnameToList m

-- | Only use this @show@ function in debugging!  To convert an
--   abstract 'QName' into a string use @prettyShow@.
instance Show QName where
  show q = concat $ intersperse "." $ map show $ qnameToList q

------------------------------------------------------------------------
-- * Pretty instances
------------------------------------------------------------------------

instance Pretty Name where
  pretty = pretty . nameConcrete

instance Pretty ModuleName where
  pretty = hcat . punctuate (text ".") . map pretty . mnameToList

instance Pretty QName where
  pretty = hcat . punctuate (text ".") . map pretty . qnameToList

instance Pretty AmbiguousQName where
  pretty (AmbQ qs) = hcat $ punctuate (text " | ") $ map pretty qs

------------------------------------------------------------------------
-- * Range instances
------------------------------------------------------------------------

-- ** HasRange

instance HasRange Name where
  getRange = getRange . nameConcrete

instance HasRange ModuleName where
  getRange (MName []) = noRange
  getRange (MName xs) = getRange xs

instance HasRange QName where
  getRange q = getRange (qnameModule q, qnameName q)

-- | The range of an @AmbiguousQName@ is the range of any of its
--   disambiguations (they are the same concrete name).
instance HasRange AmbiguousQName where
  getRange (AmbQ [])    = noRange
  getRange (AmbQ (c:_)) = getRange c

-- ** SetRange

instance SetRange Name where
  setRange r x = x { nameConcrete = setRange r $ nameConcrete x }

instance SetRange QName where
  setRange r q = q { qnameModule = setRange r $ qnameModule q
                   , qnameName   = setRange r $ qnameName   q
                   }

instance SetRange ModuleName where
  setRange r (MName ns) = MName (map (setRange r) ns)

-- ** KillRange

instance KillRange Name where
  killRange (Name a b c d) = killRange4 Name a b c d
  -- killRange x = x { nameConcrete = killRange $ nameConcrete x
  --                 -- Andreas, 2014-03-30
  --                 -- An experiment: what happens if we preserve
  --                 -- the range of the binding site, but kill all
  --                 -- other ranges before serialization?
  --                 -- Andreas, Makoto, 2014-10-18 AIM XX
  --                 -- Kill all ranges in signature, including nameBindingSite.
  --                 , nameBindingSite = noRange
  --                 }

instance KillRange ModuleName where
  killRange (MName xs) = MName $ killRange xs

instance KillRange QName where
  killRange (QName a b) = killRange2 QName a b
  -- killRange q = q { qnameModule = killRange $ qnameModule q
  --                 , qnameName   = killRange $ qnameName   q
  --                 }

instance KillRange AmbiguousQName where
  killRange (AmbQ xs) = AmbQ $ killRange xs

------------------------------------------------------------------------
-- * Sized instances
------------------------------------------------------------------------

instance Sized QName where
  size = size . qnameToList

instance Sized ModuleName where
  size = size . mnameToList
