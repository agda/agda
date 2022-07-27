{-| Names in the concrete syntax are just strings (or lists of strings for
    qualified names).
-}
module Agda.Syntax.Concrete.Name where

import Prelude hiding ((!!))

import Control.DeepSeq

import Data.ByteString.Char8 (ByteString)
import Data.Function
import qualified Data.Foldable as Fold
import qualified Data.List as List
import Data.Data (Data)

import GHC.Generics (Generic)

import System.FilePath

import Agda.Syntax.Common
import Agda.Syntax.Concrete.Glyph
import Agda.Syntax.Position

import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Utils.List  ((!!), last1)
import Agda.Utils.List1 (List1, pattern (:|), (<|))
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Pretty
import Agda.Utils.Singleton
import Agda.Utils.Size
import Agda.Utils.Suffix

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
    , nameNameParts :: NameParts
    }
  | NoName -- ^ @_@.
    { nameRange     :: Range
    , nameId        :: NameId
    }
  deriving Data

type NameParts = List1 NamePart

-- | An open mixfix identifier is either prefix, infix, or suffix.
--   That is to say: at least one of its extremities is a @Hole@

isOpenMixfix :: Name -> Bool
isOpenMixfix = \case
  Name _ _ (x :| x' : xs) -> x == Hole || last1 x' xs == Hole
  _ -> False

instance Underscore Name where
  underscore = NoName noRange __IMPOSSIBLE__
  isUnderscore NoName{} = True
  isUnderscore (Name {nameNameParts = Id x :| []}) = isUnderscore x
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
  , moduleNameParts :: List1 String
  }
  deriving (Show, Data, Generic)

instance Eq    TopLevelModuleName where (==)    = (==)    `on` moduleNameParts
instance Ord   TopLevelModuleName where compare = compare `on` moduleNameParts
instance Sized TopLevelModuleName where size    = size     .   moduleNameParts

------------------------------------------------------------------------
-- * Constructing simple 'Name's.
------------------------------------------------------------------------

-- | Create an ordinary 'InScope' name.
simpleName :: RawName -> Name
simpleName = Name noRange InScope . singleton . Id

-- | Create a binary operator name in scope.
simpleBinaryOperator :: RawName -> Name
simpleBinaryOperator s = Name noRange InScope $ Hole :| Id s : Hole : []

-- | Create an ordinary 'InScope' name containing a single 'Hole'.
simpleHole :: Name
simpleHole = Name noRange InScope $ singleton Hole

------------------------------------------------------------------------
-- * Operations on 'Name' and 'NamePart'
------------------------------------------------------------------------

-- | Don't use on 'NoName{}'.
lensNameParts :: Lens' NameParts Name
lensNameParts f = \case
  n@Name{} -> f (nameNameParts n) <&> \ ps -> n { nameNameParts = ps }
  NoName{} -> __IMPOSSIBLE__

nameToRawName :: Name -> RawName
nameToRawName = prettyShow

nameParts :: Name -> NameParts
nameParts (Name _ _ ps)    = ps
nameParts (NoName _ _)     = singleton $ Id "_" -- To not return an empty list

nameStringParts :: Name -> [RawName]
nameStringParts n = [ s | Id s <- List1.toList $ nameParts n ]

-- | Parse a string to parts of a concrete name.
--
--   Note: @stringNameParts "_" == [Id "_"] == nameParts NoName{}@

stringNameParts :: String -> NameParts
stringNameParts ""  = singleton $ Id "_"  -- NoName
stringNameParts "_" = singleton $ Id "_"  -- NoName
stringNameParts s = List1.fromList __IMPOSSIBLE__ $ loop s
  where
  loop ""                              = []
  loop ('_':s)                         = Hole : loop s
  loop s | (x, s') <- break (== '_') s = Id (stringToRawName x) : loop s'

-- | Number of holes in a 'Name' (i.e., arity of a mixfix-operator).
class NumHoles a where
  numHoles :: a -> Int

instance NumHoles NameParts where
  numHoles = length . List1.filter (== Hole)

instance NumHoles Name where
  numHoles NoName{}         = 0
  numHoles (Name { nameNameParts = parts }) = numHoles parts

instance NumHoles QName where
  numHoles (QName x)  = numHoles x
  numHoles (Qual _ x) = numHoles x

-- | Is the name an operator?
--   Needs at least 2 'NamePart's.
isOperator :: Name -> Bool
isOperator = \case
  Name _ _ (_ :| _ : _) -> True
  _ -> False

isHole :: NamePart -> Bool
isHole Hole = True
isHole _    = False

isPrefix, isPostfix, isInfix, isNonfix :: Name -> Bool
isPrefix  x = not (isHole (List1.head xs)) &&      isHole (List1.last xs)  where xs = nameParts x
isPostfix x =      isHole (List1.head xs)  && not (isHole (List1.last xs)) where xs = nameParts x
isInfix   x =      isHole (List1.head xs)  &&      isHole (List1.last xs)  where xs = nameParts x
isNonfix  x = not (isHole (List1.head xs)) && not (isHole (List1.last xs)) where xs = nameParts x


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
    n@NoName{} -> n <$ f InScope

instance LensInScope QName where
  lensInScope f = \case
    Qual x xs -> (`Qual` xs) <$> lensInScope f x
    QName x   -> QName <$> lensInScope f x

------------------------------------------------------------------------
-- * Generating fresh names
------------------------------------------------------------------------

-- | Method by which to generate fresh unshadowed names.
data FreshNameMode
  = UnicodeSubscript
  -- ^ Append an integer Unicode subscript: x, x₁, x₂, …
  | AsciiCounter
  -- ^ Append an integer ASCII counter: x, x1, x2, …

  -- Note that @Agda.Utils.Suffix@ supports an additional style, @Prime@, but
  -- we currently only encounter it when extending an existing name of that
  -- format, (x', x'', …), not for an initially-generated permutation. There's
  -- no reason we couldn't, except that we currently choose between
  -- subscript/counter styles based on the --no-unicode mode rather than any
  -- finer-grained option.
  --   | PrimeTickCount
  --   ^ Append an ASCII prime/apostrophe: x, x', x'', …

nextRawName :: FreshNameMode -> RawName -> RawName
nextRawName freshNameMode s = addSuffix root (maybe initialSuffix nextSuffix suffix)
  where
  (root, suffix) = suffixView s
  initialSuffix = case freshNameMode of
    UnicodeSubscript -> Subscript 1
    AsciiCounter -> Index 1

-- | Get the next version of the concrete name. For instance,
--   @nextName "x" = "x₁"@.  The name must not be a 'NoName'.
nextName :: FreshNameMode -> Name -> Name
nextName freshNameMode x@Name{} = setNotInScope $ over (lensNameParts . lastIdPart) (nextRawName freshNameMode) x
nextName             _ NoName{} = __IMPOSSIBLE__

-- | Zoom on the last non-hole in a name.
lastIdPart :: Lens' RawName NameParts
lastIdPart f = loop
  where
  loop = \case
    Id s :| []     -> f s <&> \ s -> Id s :| []
    Id s :| [Hole] -> f s <&> \ s -> Id s :| [Hole]
    p1 :| p2 : ps  -> (p1 <|) <$> loop (p2 :| ps)
    Hole :| []     -> __IMPOSSIBLE__

-- | Get the first version of the concrete name that does not satisfy
--   the given predicate.
firstNonTakenName :: FreshNameMode -> (Name -> Bool) -> Name -> Name
firstNonTakenName freshNameMode taken x =
  if taken x
  then firstNonTakenName freshNameMode taken (nextName freshNameMode x)
  else x

-- | Lens for accessing and modifying the suffix of a name.
--   The suffix of a @NoName@ is always @Nothing@, and should not be
--   changed.
nameSuffix :: Lens' (Maybe Suffix) Name
nameSuffix (f :: Maybe Suffix -> f (Maybe Suffix)) = \case

  n@NoName{} -> f Nothing <&> \case
    Nothing -> n
    Just {} -> __IMPOSSIBLE__

  n@Name{} -> lensNameParts (lastIdPart idSuf) n
    where
    idSuf s =
      let (root, suffix) = suffixView s
      in maybe root (addSuffix root) <$> (f suffix)

-- | Split a name into a base name plus a suffix.
nameSuffixView :: Name -> (Maybe Suffix, Name)
nameSuffixView = nameSuffix (,Nothing)

-- | Replaces the suffix of a name. Unless the suffix is @Nothing@,
--   the name should not be @NoName@.
setNameSuffix :: Maybe Suffix -> Name -> Name
setNameSuffix = set nameSuffix

-- | Get a raw version of the name with all suffixes removed. For
--   instance, @nameRoot "x₁₂₃" = "x"@.
nameRoot :: Name -> RawName
nameRoot x = nameToRawName $ snd $ nameSuffixView x

sameRoot :: Name -> Name -> Bool
sameRoot = (==) `on` nameRoot

------------------------------------------------------------------------
-- * Operations on qualified names
------------------------------------------------------------------------

-- | Lens for the unqualified part of a QName
lensQNameName :: Lens' Name QName
lensQNameName f (QName n)  = QName <$> f n
lensQNameName f (Qual m n) = Qual m <$> lensQNameName f n

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
qnameParts :: QName -> List1 Name
qnameParts (Qual x q) = x <| qnameParts q
qnameParts (QName x)  = singleton x

-- | Is the name (un)qualified?

isQualified :: QName -> Bool
isQualified Qual{}  = True
isQualified QName{} = False

isUnqualified :: QName -> Maybe Name
isUnqualified Qual{}    = Nothing
isUnqualified (QName n) = Just n

------------------------------------------------------------------------
-- * Operations on 'TopLevelModuleName'
------------------------------------------------------------------------

-- | Turns a qualified name into a 'TopLevelModuleName'. The qualified
-- name is assumed to represent a top-level module name.

toTopLevelModuleName :: QName -> TopLevelModuleName
toTopLevelModuleName q = TopLevelModuleName (getRange q) $
  fmap nameToRawName $ qnameParts q

-- | Turns a top-level module name into a file name with the given
-- suffix.

moduleNameToFileName :: TopLevelModuleName -> String -> FilePath
moduleNameToFileName (TopLevelModuleName _ ms) ext =
  joinPath (List1.init ms) </> List1.last ms <.> ext

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
    iterate takeDirectory (filePath file) !! length m

------------------------------------------------------------------------
-- * No name stuff
------------------------------------------------------------------------

-- | @noName_ = 'noName' 'noRange'@
noName_ :: Name
noName_ = noName noRange

noName :: Range -> Name
noName r = NoName r (NameId 0 noModuleNameHash)

-- | Check whether a name is the empty name "_".
class IsNoName a where
  isNoName :: a -> Bool

  default isNoName :: (Foldable t, IsNoName b, t b ~ a) => a -> Bool
  isNoName = Fold.all isNoName

instance IsNoName String where
  isNoName = isUnderscore

instance IsNoName ByteString where
  isNoName = isUnderscore

instance IsNoName Name where
  isNoName = \case
    NoName{}              -> True
    Name _ _ (Hole :| []) -> True
    Name _ _ (Id x :| []) -> isNoName x
    _ -> False

instance IsNoName QName where
  isNoName (QName x) = isNoName x
  isNoName Qual{}    = False        -- M.A._ does not qualify as empty name

instance IsNoName a => IsNoName (Ranged a) where
instance IsNoName a => IsNoName (WithOrigin a) where

-- no instance for TopLevelModuleName

------------------------------------------------------------------------
-- * Showing names
------------------------------------------------------------------------

deriving instance Show Name
deriving instance Show NamePart
deriving instance Show QName

------------------------------------------------------------------------
-- * Printing names
------------------------------------------------------------------------

instance Pretty Name where
  pretty (Name _ _ xs)    = hcat $ fmap pretty xs
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
  pretty (TopLevelModuleName _ ms) = text $ List.intercalate "." $ List1.toList ms

------------------------------------------------------------------------
-- * Range instances
------------------------------------------------------------------------

instance HasRange Name where
    getRange (Name r _ _ps) = r
    getRange (NoName r _)   = r

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

instance NFData NameInScope where
  rnf InScope    = ()
  rnf NotInScope = ()

-- | Ranges are not forced.

instance NFData Name where
  rnf (Name _ nis ns) = rnf nis `seq` rnf ns
  rnf (NoName _ n)  = rnf n

instance NFData NamePart where
  rnf Hole   = ()
  rnf (Id s) = rnf s

instance NFData QName where
  rnf (Qual a b) = rnf a `seq` rnf b
  rnf (QName a)  = rnf a

instance NFData TopLevelModuleName
