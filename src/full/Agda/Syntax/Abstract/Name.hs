
{-| Abstract names carry unique identifiers and stuff.
-}
module Agda.Syntax.Abstract.Name
  ( module Agda.Syntax.Abstract.Name
  , IsNoName(..)
  , FreshNameMode(..)
  ) where

import Prelude hiding (length)

import Control.DeepSeq

import Data.Foldable (length)
import Data.Function
import Data.Hashable (Hashable(..))
import qualified Data.List as List
import Data.Maybe
import Data.Void

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name (IsNoName(..), NumHoles(..), NameInScope(..), LensInScope(..), FreshNameMode(..))
import qualified Agda.Syntax.Concrete.Name as C

import Agda.Utils.Functor
import Agda.Utils.Lens
import qualified Agda.Utils.List as L
import Agda.Utils.List1 (List1, pattern (:|), (<|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Pretty
import Agda.Utils.Size

import Agda.Utils.Impossible

-- | A name is a unique identifier and a suggestion for a concrete name. The
--   concrete name contains the source location (if any) of the name. The
--   source location of the binding site is also recorded.
data Name = Name
  { nameId           :: !NameId
  , nameConcrete     :: C.Name  -- ^ The concrete name used for this instance
  , nameCanonical    :: C.Name  -- ^ The concrete name in the original definition (needed by primShowQName, see #4735)
  , nameBindingSite  :: Range
  , nameFixity       :: Fixity'
  , nameIsRecordName :: Bool
      -- ^ Is this the name of the invisible record variable `self`?
      --   Should not be printed or displayed in the context, see issue #3584.
  }

-- | Useful for debugging scoping problems
uglyShowName :: Name -> String
uglyShowName x = show (nameId x, nameConcrete x)

-- | Qualified names are non-empty lists of names. Equality on qualified names
--   are just equality on the last name, i.e. the module part is just
--   for show.
--
-- The 'SetRange' instance for qualified names sets all individual
-- ranges (including those of the module prefix) to the given one.
data QName = QName { qnameModule :: ModuleName
                   , qnameName   :: Name
                   }

-- | Something preceeded by a qualified name.
data QNamed a = QNamed
  { qname  :: QName
  , qnamed :: a
  }
  deriving (Functor, Foldable, Traversable)

-- | A module name is just a qualified name.
--
-- The 'SetRange' instance for module names sets all individual ranges
-- to the given one.
newtype ModuleName = MName { mnameToList :: [Name] }
  deriving (Eq, Ord)

-- | Ambiguous qualified names. Used for overloaded constructors.
--
-- Invariant: All the names in the list must have the same concrete,
-- unqualified name.  (This implies that they all have the same 'Range').
newtype AmbiguousQName = AmbQ { unAmbQ :: List1 QName }
  deriving (Eq, Ord, NFData)

-- | A singleton "ambiguous" name.
unambiguous :: QName -> AmbiguousQName
unambiguous x = AmbQ (x :| [])

-- | Get the first of the ambiguous names.
headAmbQ :: AmbiguousQName -> QName
headAmbQ (AmbQ xs) = List1.head xs

-- | Is a name ambiguous.
isAmbiguous :: AmbiguousQName -> Bool
isAmbiguous (AmbQ (_ :| xs)) = not (null xs)

-- | Get the name if unambiguous.
getUnambiguous :: AmbiguousQName -> Maybe QName
getUnambiguous (AmbQ (x :| [])) = Just x
getUnambiguous _                = Nothing

-- | A name suffix
data Suffix
  = NoSuffix
  | Suffix !Integer
  deriving (Show, Eq, Ord)

instance NFData Suffix where
  rnf NoSuffix   = ()
  rnf (Suffix _) = ()

-- | Check whether we are a projection pattern.
class IsProjP a where
  isProjP :: a -> Maybe (ProjOrigin, AmbiguousQName)

instance IsProjP a => IsProjP (Arg a) where
  isProjP p = case isProjP $ unArg p of
    Just (ProjPostfix , f)
     | getHiding p /= NotHidden -> Nothing
    x -> x

instance IsProjP a => IsProjP (Named n a) where
  isProjP = isProjP . namedThing

instance IsProjP Void where
  isProjP _ = __IMPOSSIBLE__

-- | A module is anonymous if the qualification path ends in an underscore.
isAnonymousModuleName :: ModuleName -> Bool
isAnonymousModuleName (MName mms) = maybe False isNoName $ L.lastMaybe mms

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

withRangesOf :: ModuleName -> List1 C.Name -> ModuleName
MName ms `withRangesOf` ns = if m < n then __IMPOSSIBLE__ else MName $
      zipWith setRange (replicate (m - n) noRange ++ map getRange (List1.toList ns)) ms
  where
    m = length ms
    n = length ns

-- | Like 'withRangesOf', but uses the name parts (qualifier + name)
-- of the qualified name as the list of concrete names.

withRangesOfQ :: ModuleName -> C.QName -> ModuleName
m `withRangesOfQ` q = m `withRangesOf` C.qnameParts q

mnameFromList :: [Name] -> ModuleName
mnameFromList = MName

mnameFromList1 :: List1 Name -> ModuleName
mnameFromList1 = MName . List1.toList

mnameToList1 :: ModuleName -> List1 Name
mnameToList1 (MName ns) = List1.ifNull ns __IMPOSSIBLE__ id

noModuleName :: ModuleName
noModuleName = mnameFromList []

commonParentModule :: ModuleName -> ModuleName -> ModuleName
commonParentModule m1 m2 =
  mnameFromList $ L.commonPrefix (mnameToList m1) (mnameToList m2)

-- | Make a 'Name' from some kind of string.
class MkName a where
  -- | The 'Range' sets the /definition site/ of the name, not the use site.
  mkName :: Range -> NameId -> a -> Name

  mkName_ :: NameId -> a -> Name
  mkName_ = mkName noRange

instance MkName String where
  mkName r i s = makeName i (C.Name noRange InScope (C.stringNameParts s)) r noFixity' False

makeName :: NameId -> C.Name -> Range -> Fixity' -> Bool -> Name
makeName i c r f rec = Name i c c r f rec

qnameToList0 :: QName -> [Name]
qnameToList0 = List1.toList . qnameToList

qnameToList :: QName -> List1 Name
qnameToList (QName m x) = mnameToList m `List1.snoc` x

qnameFromList :: List1 Name -> QName
qnameFromList xs = QName (mnameFromList $ List1.init xs) (List1.last xs)

qnameToMName :: QName -> ModuleName
qnameToMName = mnameFromList1 . qnameToList

mnameToQName :: ModuleName -> QName
mnameToQName = qnameFromList . mnameToList1

showQNameId :: QName -> String
showQNameId q = show ns ++ "@" ++ show m
  where
    is = map nameId $ mnameToList (qnameModule q) ++ [qnameName q]
    ns = [ n | NameId n _ <- is ]
    m  = head [ m | NameId _ m <- is ]

-- | Turn a qualified name into a concrete name. This should only be used as a
--   fallback when looking up the right concrete name in the scope fails.
qnameToConcrete :: QName -> C.QName
qnameToConcrete (QName m x) =       -- Use the canonical name here (#5048)
   foldr (C.Qual . nameConcrete) (C.QName $ nameCanonical x) (mnameToList m)

mnameToConcrete :: ModuleName -> C.QName
mnameToConcrete (MName []) = __IMPOSSIBLE__ -- C.QName C.noName_  -- should never happen?
mnameToConcrete (MName (x:xs)) = foldr C.Qual (C.QName $ List1.last cs) $ List1.init cs
  where
    cs = fmap nameConcrete (x :| xs)

-- | Computes the 'TopLevelModuleName' corresponding to the given
-- module name, which is assumed to represent a top-level module name.
--
-- Precondition: The module name must be well-formed.

toTopLevelModuleName :: ModuleName -> C.TopLevelModuleName
toTopLevelModuleName (MName []) = __IMPOSSIBLE__
toTopLevelModuleName (MName ms) = List1.ifNull ms __IMPOSSIBLE__ {-else-} $ \ ms1 ->
  C.TopLevelModuleName (getRange ms1) $ fmap (C.nameToRawName . nameConcrete) ms1

qualifyM :: ModuleName -> ModuleName -> ModuleName
qualifyM m1 m2 = mnameFromList $ mnameToList m1 ++ mnameToList m2

qualifyQ :: ModuleName -> QName -> QName
qualifyQ m x = qnameFromList $ mnameToList m `List1.prependList` qnameToList x

qualify :: ModuleName -> Name -> QName
qualify = QName

-- | Convert a 'Name' to a 'QName' (add no module name).
qualify_ :: Name -> QName
qualify_ = qualify noModuleName

-- | Is the name an operator?

isOperator :: QName -> Bool
isOperator = C.isOperator . nameConcrete . qnameName

-- | Is the first module a weak parent of the second?
isLeParentModuleOf :: ModuleName -> ModuleName -> Bool
isLeParentModuleOf = List.isPrefixOf `on` mnameToList

-- | Is the first module a proper parent of the second?
isLtParentModuleOf :: ModuleName -> ModuleName -> Bool
isLtParentModuleOf x y =
  isJust $ (L.stripPrefixBy (==) `on` mnameToList) x y

-- | Is the first module a weak child of the second?
isLeChildModuleOf :: ModuleName -> ModuleName -> Bool
isLeChildModuleOf = flip isLeParentModuleOf

-- | Is the first module a proper child of the second?
isLtChildModuleOf :: ModuleName -> ModuleName -> Bool
isLtChildModuleOf = flip isLtParentModuleOf

isInModule :: QName -> ModuleName -> Bool
isInModule q m = mnameToList m `List.isPrefixOf` qnameToList0 q

-- | Get the next version of the concrete name. For instance, @nextName "x" = "x₁"@.
--   The name must not be a 'NoName'.
nextName :: C.FreshNameMode -> Name -> Name
nextName freshNameMode x = x { nameConcrete = C.nextName freshNameMode (nameConcrete x) }

sameRoot :: Name -> Name -> Bool
sameRoot = C.sameRoot `on` nameConcrete

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

instance NumHoles Name where
  numHoles = numHoles . nameConcrete

instance NumHoles QName where
  numHoles = numHoles . qnameName

-- | We can have an instance for ambiguous names as all share a common concrete name.
instance NumHoles AmbiguousQName where
  numHoles = numHoles . headAmbQ

------------------------------------------------------------------------
-- * name lenses
------------------------------------------------------------------------

lensQNameName :: Lens' Name QName
lensQNameName f (QName m n) = QName m <$> f n

------------------------------------------------------------------------
-- * LensFixity' instances
------------------------------------------------------------------------

instance LensFixity' Name where
  lensFixity' f n = f (nameFixity n) <&> \ fix' -> n { nameFixity = fix' }

instance LensFixity' QName where
  lensFixity' = lensQNameName . lensFixity'

------------------------------------------------------------------------
-- * LensFixity instances
------------------------------------------------------------------------

instance LensFixity Name where
  lensFixity = lensFixity' . lensFixity

instance LensFixity QName where
  lensFixity = lensFixity' . lensFixity

------------------------------------------------------------------------
-- * LensInScope instances
------------------------------------------------------------------------

instance LensInScope Name where
  lensInScope f n@Name{ nameConcrete = x } =
    (\y -> n { nameConcrete = y }) <$> lensInScope f x

instance LensInScope QName where
  lensInScope f q@QName{ qnameName = n } =
    (\n' -> q { qnameName = n' }) <$> lensInScope f n

------------------------------------------------------------------------
-- * Show instances (only for debug printing!)
--
-- | Use 'prettyShow' to print names to the user.
------------------------------------------------------------------------

deriving instance Show Name
deriving instance Show ModuleName
deriving instance Show QName
deriving instance Show a => Show (QNamed a)
deriving instance Show AmbiguousQName

nameToArgName :: Name -> ArgName
nameToArgName = stringToArgName . prettyShow

namedArgName :: NamedArg Name -> ArgName
namedArgName x = fromMaybe (nameToArgName $ namedArg x) $ bareNameOf x

------------------------------------------------------------------------
-- * Pretty instances
------------------------------------------------------------------------

instance Pretty Name where
  pretty = pretty . nameConcrete

instance Pretty ModuleName where
  pretty = hcat . punctuate "." . map pretty . mnameToList

instance Pretty QName where
  pretty = hcat . punctuate "." . map pretty . qnameToList0 . useCanonical
    where
      -- #4735: When printing a fully qualified name (as done by primShowQName) we need to
      -- use the origincal concrete name, not the possibly renamed concrete name in 'nameConcrete'.
      useCanonical q = q { qnameName = (qnameName q) { nameConcrete = nameCanonical (qnameName q) } }

instance Pretty AmbiguousQName where
  pretty (AmbQ qs) = hcat $ punctuate " | " $ map pretty $ List1.toList qs

instance Pretty a => Pretty (QNamed a) where
  pretty (QNamed a b) = pretty a <> "." <> pretty b

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
  getRange (AmbQ (c :| _)) = getRange c

-- ** SetRange

instance SetRange Name where
  setRange r x = x { nameConcrete = setRange r $ nameConcrete x }

instance SetRange QName where
  setRange r q = q { qnameModule = setRange r $ qnameModule q
                   , qnameName   = setRange r $ qnameName   q
                   }

instance SetRange ModuleName where
  setRange r (MName ns) = MName (zipWith setRange rs ns)
    where
      -- Put the range only on the last name. Otherwise
      -- we get overlapping jump-to-definition links for all
      -- the parts (See #2666).
      rs = replicate (length ns - 1) noRange ++ [r]

-- ** KillRange

instance KillRange Name where
  killRange (Name a b c d e f) =
    (killRange6 Name a b c d e f) { nameBindingSite = d }
    -- Andreas, 2017-07-25, issue #2649
    -- Preserve the nameBindingSite for error message.
    --
    -- Older remarks:
    --
    -- Andreas, 2014-03-30
    -- An experiment: what happens if we preserve
    -- the range of the binding site, but kill all
    -- other ranges before serialization?
    --
    -- Andreas, Makoto, 2014-10-18 AIM XX
    -- Kill all ranges in signature, including nameBindingSite.

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

------------------------------------------------------------------------
-- * NFData instances
------------------------------------------------------------------------

-- | The range is not forced.

instance NFData Name where
  rnf (Name _ a b _ c d) = rnf (a, b, c, d)

instance NFData QName where
  rnf (QName a b) = rnf a `seq` rnf b

instance NFData ModuleName where
  rnf (MName a) = rnf a
