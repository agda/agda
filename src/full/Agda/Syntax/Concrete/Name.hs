{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| Names in the concrete syntax are just strings (or lists of strings for
    qualified names).
-}
module Agda.Syntax.Concrete.Name where

#if MIN_VERSION_base(4,11,0)
import Prelude hiding ((<>))
#endif

import Control.DeepSeq

import Data.ByteString.Char8 (ByteString)
import Data.Function
import qualified Data.List as List
import Data.Data (Data)
import Data.Maybe

import GHC.Generics (Generic)

import System.FilePath

import Agda.Syntax.Common
import Agda.Syntax.Position

import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Pretty
import Agda.Utils.Size
import Agda.Utils.Suffix

#include "undefined.h"
import Agda.Utils.Impossible

{-| A name is a non-empty list of alternating 'Id's and 'Hole's. A normal name
    is represented by a singleton list, and operators are represented by a list
    with 'Hole's where the arguments should go. For instance: @[Hole,Id "+",Hole]@
    is infix addition.

    Equality and ordering on @Name@s are defined to ignore range so same names
    in different locations are equal.
-}
data Name
  = Name -- ^ A (mixfix) identifier.
    { nameRange     :: Range
    , nameInScope   :: NameInScope
    , nameNameParts :: [NamePart]
    }
  | NoName -- ^ @_@.
    { nameRange     :: Range
    , nameId        :: NameId
    }
  deriving Data

-- | An open mixfix identifier is either prefix, infix, or suffix.
--   That is to say: at least one of its extremities is a @Hole@

isOpenMixfix :: Name -> Bool
isOpenMixfix n = case n of
  Name _ _ (x : xs@(_:_)) -> x == Hole || last xs == Hole
  _                       -> False

instance Underscore Name where
  underscore = NoName noRange __IMPOSSIBLE__
  isUnderscore NoName{} = True
  isUnderscore (Name {nameNameParts = [Id x]}) = isUnderscore x
  isUnderscore _ = False

-- | Mixfix identifiers are composed of words and holes,
--   e.g. @_+_@ or @if_then_else_@ or @[_/_]@.
data NamePart
  = Hole       -- ^ @_@ part.
  | Id RawName  -- ^ Identifier part.
  deriving (Data, Generic)

-- | Define equality on @Name@ to ignore range so same names in different
--   locations are equal.
--
--   Is there a reason not to do this? -Jeff
--
--   No. But there are tons of reasons to do it. For instance, when using
--   names as keys in maps you really don't want to have to get the range
--   right to be able to do a lookup. -Ulf

instance Eq Name where
    Name _ _ xs    == Name _ _ ys    = xs == ys
    NoName _ i     == NoName _ j     = i == j
    _              == _              = False

instance Ord Name where
    compare (Name _ _ xs)  (Name _ _ ys)      = compare xs ys
    compare (NoName _ i)   (NoName _ j)       = compare i j
    compare (NoName {})    (Name {})          = LT
    compare (Name {})      (NoName {})        = GT

instance Eq NamePart where
  Hole  == Hole  = True
  Id s1 == Id s2 = s1 == s2
  _     == _     = False

instance Ord NamePart where
  compare Hole    Hole    = EQ
  compare Hole    (Id {}) = LT
  compare (Id {}) Hole    = GT
  compare (Id s1) (Id s2) = compare s1 s2

-- | @QName@ is a list of namespaces and the name of the constant.
--   For the moment assumes namespaces are just @Name@s and not
--     explicitly applied modules.
--   Also assumes namespaces are generative by just using derived
--     equality. We will have to define an equality instance to
--     non-generative namespaces (as well as having some sort of
--     lookup table for namespace names).
data QName
  = Qual  Name QName -- ^ @A.rest@.
  | QName Name       -- ^ @x@.
  deriving (Data, Eq, Ord)

instance Underscore QName where
  underscore = QName underscore
  isUnderscore (QName x) = isUnderscore x
  isUnderscore Qual{}    = False

-- | Top-level module names.  Used in connection with the file system.
--
--   Invariant: The list must not be empty.

data TopLevelModuleName = TopLevelModuleName
  { moduleNameRange :: Range
  , moduleNameParts :: [String]
  }
  deriving (Show, Data)

instance Eq    TopLevelModuleName where (==)    = (==)    `on` moduleNameParts
instance Ord   TopLevelModuleName where compare = compare `on` moduleNameParts
instance Sized TopLevelModuleName where size    = size     .   moduleNameParts

------------------------------------------------------------------------
-- * Operations on 'Name' and 'NamePart'
------------------------------------------------------------------------

nameToRawName :: Name -> RawName
nameToRawName = prettyShow

nameParts :: Name -> [NamePart]
nameParts (Name _ _ ps)    = ps
nameParts (NoName _ _)     = [Id "_"] -- To not return an empty list

nameStringParts :: Name -> [RawName]
nameStringParts n = [ s | Id s <- nameParts n ]

-- | Parse a string to parts of a concrete name.
--
--   Note: @stringNameParts "_" == [Id "_"] == nameParts NoName{}@

stringNameParts :: String -> [NamePart]
stringNameParts "_" = [Id "_"]   -- NoName
stringNameParts s = loop s where
  loop ""                              = []
  loop ('_':s)                         = Hole : loop s
  loop s | (x, s') <- break (== '_') s = Id (stringToRawName x) : loop s'

-- | Number of holes in a 'Name' (i.e., arity of a mixfix-operator).
class NumHoles a where
  numHoles :: a -> Int

instance NumHoles [NamePart] where
  numHoles = length . filter (== Hole)

instance NumHoles Name where
  numHoles NoName{}         = 0
  numHoles (Name { nameNameParts = parts }) = numHoles parts

instance NumHoles QName where
  numHoles (QName x)  = numHoles x
  numHoles (Qual _ x) = numHoles x

-- | Is the name an operator?

isOperator :: Name -> Bool
isOperator (NoName {})     = False
isOperator (Name _ _ ps)   = length ps > 1

isHole :: NamePart -> Bool
isHole Hole = True
isHole _    = False

isPrefix, isPostfix, isInfix, isNonfix :: Name -> Bool
isPrefix  x = not (isHole (head xs)) &&      isHole (last xs)  where xs = nameParts x
isPostfix x =      isHole (head xs)  && not (isHole (last xs)) where xs = nameParts x
isInfix   x =      isHole (head xs)  &&      isHole (last xs)  where xs = nameParts x
isNonfix  x = not (isHole (head xs)) && not (isHole (last xs)) where xs = nameParts x


------------------------------------------------------------------------
-- * Keeping track of which names are (not) in scope
------------------------------------------------------------------------

data NameInScope = InScope | NotInScope
  deriving (Eq, Show, Data)

class LensInScope a where
  lensInScope :: Lens' NameInScope a

  isInScope :: a -> NameInScope
  isInScope x = x ^. lensInScope

  mapInScope :: (NameInScope -> NameInScope) -> a -> a
  mapInScope = over lensInScope

  setInScope :: a -> a
  setInScope = mapInScope $ const InScope

  setNotInScope :: a -> a
  setNotInScope = mapInScope $ const NotInScope

instance LensInScope NameInScope where
  lensInScope = id

instance LensInScope Name where
  lensInScope f = \case
    n@Name{ nameInScope = nis } -> (\nis' -> n { nameInScope = nis' }) <$> f nis
    n@NoName{} -> const n <$> f InScope

instance LensInScope QName where
  lensInScope f = \case
    Qual x xs -> (`Qual` xs) <$> lensInScope f x
    QName x   -> QName <$> lensInScope f x

------------------------------------------------------------------------
-- * Generating fresh names
------------------------------------------------------------------------

nextStr :: String -> String
nextStr s = case suffixView s of
  (s0, suf) -> addSuffix s0 (nextSuffix suf)

-- | Get the next version of the concrete name. For instance,
--   @nextName "x" = "x₁"@.  The name must not be a 'NoName'.
nextName :: Name -> Name
nextName NoName{} = __IMPOSSIBLE__
nextName x@Name{ nameNameParts = ps } = x { nameInScope = NotInScope, nameNameParts = nextSuf ps }
  where
    nextSuf [Id s]       = [Id $ nextStr s]
    nextSuf [Id s, Hole] = [Id $ nextStr s, Hole]
    nextSuf (p : ps)     = p : nextSuf ps
    nextSuf []           = __IMPOSSIBLE__

-- | Get the first version of the concrete name that does not satisfy
--   the given predicate.
firstNonTakenName :: (Name -> Bool) -> Name -> Name
firstNonTakenName taken x =
  if taken x
  then firstNonTakenName taken (nextName x)
  else x

-- | Get a raw version of the name with all suffixes removed. For
--   instance, @nameRoot "x₁₂₃" = "x"@. The name must not be a
--   'NoName'.
nameRoot :: Name -> RawName
nameRoot NoName{} = __IMPOSSIBLE__
nameRoot x@Name{ nameNameParts = ps } =
    nameToRawName $ x{ nameNameParts = root ps }
  where
    root [Id s] = [Id $ strRoot s]
    root [Id s, Hole] = [Id $ strRoot s , Hole]
    root (p : ps) = p : root ps
    root [] = __IMPOSSIBLE__
    strRoot = fst . suffixView

sameRoot :: Name -> Name -> Bool
sameRoot = (==) `on` nameRoot

------------------------------------------------------------------------
-- * Operations on qualified names
------------------------------------------------------------------------

-- | @qualify A.B x == A.B.x@
qualify :: QName -> Name -> QName
qualify (QName m) x     = Qual m (QName x)
qualify (Qual m m') x   = Qual m $ qualify m' x

-- | @unqualify A.B.x == x@
--
-- The range is preserved.
unqualify :: QName -> Name
unqualify q = unqualify' q `withRangeOf` q
  where
  unqualify' (QName x)  = x
  unqualify' (Qual _ x) = unqualify' x

-- | @qnameParts A.B.x = [A, B, x]@
qnameParts :: QName -> [Name]
qnameParts (Qual x q) = x : qnameParts q
qnameParts (QName x)  = [x]

-- | Is the name qualified?

isQualified :: QName -> Bool
isQualified Qual{}  = True
isQualified QName{} = False

------------------------------------------------------------------------
-- * Operations on 'TopLevelModuleName'
------------------------------------------------------------------------

-- | Turns a qualified name into a 'TopLevelModuleName'. The qualified
-- name is assumed to represent a top-level module name.

toTopLevelModuleName :: QName -> TopLevelModuleName
toTopLevelModuleName q = TopLevelModuleName (getRange q) $ map prettyShow $ qnameParts q

-- UNUSED
-- -- | Turns a top level module into a qualified name with 'noRange'.

-- fromTopLevelModuleName :: TopLevelModuleName -> QName
-- fromTopLevelModuleName (TopLevelModuleName _ [])     = __IMPOSSIBLE__
-- fromTopLevelModuleName (TopLevelModuleName _ (x:xs)) = loop x xs
--   where
--   loop x []       = QName (mk x)
--   loop x (y : ys) = Qual  (mk x) $ loop y ys
--   mk :: String -> Name
--   mk x = Name noRange [Id x]

-- | Turns a top-level module name into a file name with the given
-- suffix.

moduleNameToFileName :: TopLevelModuleName -> String -> FilePath
moduleNameToFileName (TopLevelModuleName _ []) ext = __IMPOSSIBLE__
moduleNameToFileName (TopLevelModuleName _ ms) ext =
  joinPath (init ms) </> last ms <.> ext

-- | Finds the current project's \"root\" directory, given a project
-- file and the corresponding top-level module name.
--
-- Example: If the module \"A.B.C\" is located in the file
-- \"/foo/A/B/C.agda\", then the root is \"/foo/\".
--
-- Precondition: The module name must be well-formed.

projectRoot :: AbsolutePath -> TopLevelModuleName -> AbsolutePath
projectRoot file (TopLevelModuleName _ m) =
  mkAbsolute $
  foldr (.) id (replicate (length m - 1) takeDirectory) $
  takeDirectory $
  filePath file

------------------------------------------------------------------------
-- * No name stuff
------------------------------------------------------------------------

-- | @noName_ = 'noName' 'noRange'@
noName_ :: Name
noName_ = noName noRange

noName :: Range -> Name
noName r = NoName r (NameId 0 0)

-- | Check whether a name is the empty name "_".
class IsNoName a where
  isNoName :: a -> Bool

instance IsNoName String where
  isNoName = isUnderscore

instance IsNoName ByteString where
  isNoName = isUnderscore

instance IsNoName Name where
  isNoName (NoName _ _)      = True
  isNoName (Name _ _ [Hole]) = True   -- TODO: Track down where these come from
  isNoName (Name _ _ [])     = True
  isNoName (Name _ _ [Id x]) = isNoName x
  isNoName _                 = False

instance IsNoName QName where
  isNoName (QName x) = isNoName x
  isNoName Qual{}    = False        -- M.A._ does not qualify as empty name

-- no instance for TopLevelModuleName

------------------------------------------------------------------------
-- * Showing names
------------------------------------------------------------------------

-- deriving instance Show Name
-- deriving instance Show NamePart
-- deriving instance Show QName

-- TODO: 'Show' should output Haskell-parseable representations.
-- The following instances are deprecated, and Pretty should be used
-- instead.  Later, simply derive Show for these types:

instance Show Name where
  show = prettyShow

instance Show NamePart where
  show = prettyShow

instance Show QName where
  show = prettyShow

------------------------------------------------------------------------
-- * Printing names
------------------------------------------------------------------------

instance Pretty Name where
  pretty (Name _ _ xs)    = hcat $ map pretty xs
  pretty (NoName _ _)     = "_"

instance Pretty NamePart where
  pretty Hole   = "_"
  pretty (Id s) = text $ rawNameToString s

instance Pretty QName where
  pretty (Qual m x)
    | isUnderscore m = pretty x -- don't print anonymous modules
    | otherwise      = pretty m <> "." <> pretty x
  pretty (QName x)  = pretty x

instance Pretty TopLevelModuleName where
  pretty (TopLevelModuleName _ ms) = text $ List.intercalate "." ms

------------------------------------------------------------------------
-- * Range instances
------------------------------------------------------------------------

instance HasRange Name where
    getRange (Name r _ ps)    = r
    getRange (NoName r _)     = r

instance HasRange QName where
    getRange (QName  x) = getRange x
    getRange (Qual n x) = fuseRange n x

instance HasRange TopLevelModuleName where
  getRange = moduleNameRange

instance SetRange Name where
  setRange r (Name _ nis ps) = Name r nis ps
  setRange r (NoName _ i)  = NoName r i

instance SetRange QName where
  setRange r (QName x)  = QName (setRange r x)
  setRange r (Qual n x) = Qual (setRange r n) (setRange r x)

instance SetRange TopLevelModuleName where
  setRange r (TopLevelModuleName _ x) = TopLevelModuleName r x

instance KillRange QName where
  killRange (QName x) = QName $ killRange x
  killRange (Qual n x) = killRange n `Qual` killRange x

instance KillRange Name where
  killRange (Name r nis ps)  = Name (killRange r) nis ps
  killRange (NoName r i)     = NoName (killRange r) i

instance KillRange TopLevelModuleName where
  killRange (TopLevelModuleName _ x) = TopLevelModuleName noRange x

------------------------------------------------------------------------
-- * NFData instances
------------------------------------------------------------------------

-- | Ranges are not forced.

instance NFData NameInScope where
  rnf InScope    = ()
  rnf NotInScope = ()

instance NFData Name where
  rnf (Name _ nis ns) = rnf nis `seq` rnf ns
  rnf (NoName _ n)  = rnf n

instance NFData NamePart where
  rnf Hole   = ()
  rnf (Id s) = rnf s

instance NFData QName where
  rnf (Qual a b) = rnf a `seq` rnf b
  rnf (QName a)  = rnf a
