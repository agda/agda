{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-| Some common syntactic entities are defined in this module.
-}
module Agda.Syntax.Common where

import Control.Applicative
import Control.DeepSeq

import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as ByteString
import Data.Foldable
import Data.Hashable
import qualified Data.Strict.Maybe as Strict
import Data.Semigroup hiding (Arg)
import Data.Traversable
import Data.Typeable (Typeable)
import Data.Word

import GHC.Generics (Generic)

import Agda.Syntax.Position

import Agda.Utils.Functor
import Agda.Utils.Pretty hiding ((<>))

#include "undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Delayed
---------------------------------------------------------------------------

-- | Used to specify whether something should be delayed.
data Delayed = Delayed | NotDelayed
  deriving (Typeable, Show, Eq, Ord)

instance KillRange Delayed where
  killRange = id

---------------------------------------------------------------------------
-- * Induction
---------------------------------------------------------------------------

data Induction = Inductive | CoInductive
  deriving (Typeable, Eq, Ord)

instance Show Induction where
  show Inductive   = "inductive"
  show CoInductive = "coinductive"

instance HasRange Induction where
  getRange _ = noRange

instance KillRange Induction where
  killRange = id

instance NFData Induction where
  rnf Inductive   = ()
  rnf CoInductive = ()

---------------------------------------------------------------------------
-- * Hiding
---------------------------------------------------------------------------

data Hiding  = Hidden | Instance | NotHidden
  deriving (Typeable, Show, Eq, Ord)

-- | 'Hiding' is an idempotent partial monoid, with unit 'NotHidden'.
--   'Instance' and 'NotHidden' are incompatible.
instance Semigroup Hiding where
  NotHidden <> h         = h
  h         <> NotHidden = h
  Hidden    <> Hidden    = Hidden
  Instance  <> Instance  = Instance
  _         <> _         = __IMPOSSIBLE__

instance Monoid Hiding where
  mempty = NotHidden
  mappend = (<>)

instance KillRange Hiding where
  killRange = id

instance NFData Hiding where
  rnf Hidden    = ()
  rnf Instance  = ()
  rnf NotHidden = ()

-- | Decorating something with 'Hiding' information.
data WithHiding a = WithHiding !Hiding a
  deriving (Typeable, Eq, Ord, Show, Functor, Foldable, Traversable)

instance Decoration WithHiding where
  traverseF f (WithHiding h a) = WithHiding h <$> f a

instance Applicative WithHiding where
  pure = WithHiding mempty
  WithHiding h f <*> WithHiding h' a = WithHiding (mappend h h') (f a)

instance HasRange a => HasRange (WithHiding a) where
  getRange = getRange . dget

instance SetRange a => SetRange (WithHiding a) where
  setRange = fmap . setRange

instance KillRange a => KillRange (WithHiding a) where
  killRange = fmap killRange

instance NFData a => NFData (WithHiding a) where
  rnf (WithHiding _ a) = rnf a

-- | A lens to access the 'Hiding' attribute in data structures.
--   Minimal implementation: @getHiding@ and one of @setHiding@ or @mapHiding@.
class LensHiding a where

  getHiding :: a -> Hiding

  setHiding :: Hiding -> a -> a
  setHiding h = mapHiding (const h)

  mapHiding :: (Hiding -> Hiding) -> a -> a
  mapHiding f a = setHiding (f $ getHiding a) a

instance LensHiding Hiding where
  getHiding = id
  setHiding = const
  mapHiding = id

instance LensHiding (WithHiding a) where
  getHiding   (WithHiding h _) = h
  setHiding h (WithHiding _ a) = WithHiding h a
  mapHiding f (WithHiding h a) = WithHiding (f h) a

-- | Monoidal composition of 'Hiding' information in some data.
mergeHiding :: LensHiding a => WithHiding a -> a
mergeHiding (WithHiding h a) = mapHiding (mappend h) a

-- | 'NotHidden' arguments are @visible@.
visible :: LensHiding a => a -> Bool
visible a = getHiding a == NotHidden

-- | 'Instance' and 'Hidden' arguments are @notVisible@.
notVisible :: LensHiding a => a -> Bool
notVisible a = getHiding a /= NotHidden

hide :: LensHiding a => a -> a
hide = setHiding Hidden

hideOrKeepInstance :: LensHiding a => a -> a
hideOrKeepInstance x =
  case getHiding x of
    Hidden -> x
    Instance -> x
    NotHidden -> setHiding Hidden x

makeInstance :: LensHiding a => a -> a
makeInstance = setHiding Instance

---------------------------------------------------------------------------
-- * Relevance
---------------------------------------------------------------------------

-- | An constructor argument is big if the sort of its type is bigger than
--   the sort of the data type.  Only parameters (and maybe forced arguments)
--   are allowed to be big.
--   @
--      List : Set -> Set
--      nil  : (A : Set) -> List A
--   @
--   @A@ is big in constructor @nil@ as the sort @Set1@ of its type @Set@
--   is bigger than the sort @Set@ of the data type @List@.
data Big = Big | Small
  deriving (Typeable, Show, Eq, Enum, Bounded)

instance Ord Big where
  Big <= Small = False
  _   <= _     = True

instance NFData Big where
  rnf Big   = ()
  rnf Small = ()

-- | A function argument can be relevant or irrelevant.
--   See "Agda.TypeChecking.Irrelevance".
data Relevance
  = Relevant    -- ^ The argument is (possibly) relevant at compile-time.
  | NonStrict   -- ^ The argument may never flow into evaluation position.
                --   Therefore, it is irrelevant at run-time.
                --   It is treated relevantly during equality checking.
  | Irrelevant  -- ^ The argument is irrelevant at compile- and runtime.
  | Forced Big  -- ^ The argument can be skipped during equality checking
                --   because its value is already determined by the type.
                --   If a constructor argument is big, it has to be regarded
                --   absent, otherwise we get into paradoxes.
    deriving (Typeable, Show, Eq)

allRelevances :: [Relevance]
allRelevances =
  [ Relevant
  , NonStrict
  , Irrelevant
  , Forced Small
  , Forced Big
  ]

instance KillRange Relevance where
  killRange rel = rel -- no range to kill

instance Ord Relevance where
  (<=) = moreRelevant

instance NFData Relevance where
  rnf Relevant   = ()
  rnf NonStrict  = ()
  rnf Irrelevant = ()
  rnf (Forced a) = rnf a

-- | A lens to access the 'Relevance' attribute in data structures.
--   Minimal implementation: @getRelevance@ and one of @setRelevance@ or @mapRelevance@.
class LensRelevance a where

  getRelevance :: a -> Relevance

  setRelevance :: Relevance -> a -> a
  setRelevance h = mapRelevance (const h)

  mapRelevance :: (Relevance -> Relevance) -> a -> a
  mapRelevance f a = setRelevance (f $ getRelevance a) a

instance LensRelevance Relevance where
  getRelevance = id
  setRelevance = const
  mapRelevance = id

isRelevant :: LensRelevance a => a -> Bool
isRelevant a = getRelevance a == Relevant

isIrrelevant :: LensRelevance a => a -> Bool
isIrrelevant a = getRelevance a == Irrelevant

-- | Information ordering.
-- @Relevant  \`moreRelevant\`
--  Forced    \`moreRelevant\`
--  NonStrict \`moreRelevant\`
--  Irrelevant@
moreRelevant :: Relevance -> Relevance -> Bool
moreRelevant r r' =
  case (r, r') of
    -- top
    (_, Irrelevant) -> True
    (Irrelevant, _) -> False
    -- bottom
    (Relevant, _)   -> True
    (_, Relevant)   -> False
    -- second bottom
    (Forced{}, _)   -> True
    (_, Forced{})   -> False
    -- remaining case
    (NonStrict,NonStrict) -> True

irrelevant :: Relevance -> Bool
irrelevant r =
  case r of
    Irrelevant -> True
    NonStrict  -> False
    Relevant   -> False
    Forced{}   -> False

-- | @unusableRelevance rel == True@ iff we cannot use a variable of @rel@.
unusableRelevance :: LensRelevance a => a -> Bool
unusableRelevance a = case getRelevance a of
  Irrelevant -> True
  NonStrict  -> True
  Forced{}   -> False -- @Forced@ has no semantic relevance
  Relevant   -> False

-- | 'Relevance' composition.
--   'Irrelevant' is dominant, 'Relevant' is neutral.
composeRelevance :: Relevance -> Relevance -> Relevance
composeRelevance r r' =
  case (r, r') of
    (Irrelevant, _) -> Irrelevant
    (_, Irrelevant) -> Irrelevant
    (NonStrict, _)  -> NonStrict
    (_, NonStrict)  -> NonStrict
    (Forced b, Forced b') -> Forced (max b b')  -- prefer Big over Small
    (Forced b, _)     -> Forced b
    (_, Forced b)     -> Forced b
    (Relevant, Relevant) -> Relevant

-- | @inverseComposeRelevance r x@ returns the most irrelevant @y@
--   such that forall @x@, @y@ we have
--   @x \`moreRelevant\` (r \`composeRelevance\` y)@
--   iff
--   @(r \`inverseComposeRelevance\` x) \`moreRelevant\` y@ (Galois connection).
inverseComposeRelevance :: Relevance -> Relevance -> Relevance
inverseComposeRelevance r x =
  case (r, x) of
    (Relevant, x)        -> x          -- going to relevant arg.: nothing changes
    _ | r == x           -> Relevant   -- because Relevant is comp.-neutral
    (Forced{}, Forced{}) -> Relevant   -- same, but (==) does not ignore Big
    (Forced{}, x)          -> x
    (Irrelevant, x)      -> Relevant   -- going irrelevant: every thing usable
    (_, Irrelevant)      -> Irrelevant -- otherwise: irrelevant things remain unusable
    (NonStrict, _)       -> Relevant   -- but @NonStrict@s become usable

-- | For comparing @Relevance@ ignoring @Forced@.
ignoreForced :: Relevance -> Relevance
ignoreForced Forced{}   = Relevant
ignoreForced Relevant   = Relevant
ignoreForced NonStrict  = NonStrict
ignoreForced Irrelevant = Irrelevant

-- | Irrelevant function arguments may appear non-strictly in the codomain type.
irrToNonStrict :: Relevance -> Relevance
irrToNonStrict Irrelevant = NonStrict
-- irrToNonStrict NonStrict  = Relevant -- TODO: this is bad if we apply irrToNonStrict several times!
irrToNonStrict rel        = rel

-- | Applied when working on types (unless --experimental-irrelevance).
nonStrictToRel :: Relevance -> Relevance
nonStrictToRel NonStrict = Relevant
nonStrictToRel rel       = rel

nonStrictToIrr :: Relevance -> Relevance
nonStrictToIrr NonStrict = Irrelevant
nonStrictToIrr rel       = rel

---------------------------------------------------------------------------
-- * Origin of arguments (user-written, inserted or reflected)
---------------------------------------------------------------------------

data Origin = UserWritten | Inserted | Reflected
  deriving (Typeable, Show, Eq, Ord)

instance KillRange Origin where
  killRange = id

instance NFData Origin where
  rnf UserWritten = ()
  rnf Inserted = ()
  rnf Reflected = ()

class LensOrigin a where

  getOrigin :: a -> Origin

  setOrigin :: Origin -> a -> a
  setOrigin o = mapOrigin (const o)

  mapOrigin :: (Origin -> Origin) -> a -> a
  mapOrigin f a = setOrigin (f $ getOrigin a) a

instance LensOrigin Origin where
  getOrigin = id
  setOrigin = const
  mapOrigin = id

---------------------------------------------------------------------------
-- * Argument decoration
---------------------------------------------------------------------------

-- | A function argument can be hidden and/or irrelevant.

data ArgInfo = ArgInfo
  { argInfoHiding       :: Hiding
  , argInfoRelevance    :: Relevance
  , argInfoOrigin       :: Origin
  , argInfoOverlappable :: Bool
  } deriving (Typeable, Eq, Ord, Show)

instance KillRange ArgInfo where
  killRange (ArgInfo h r o v) = killRange3 ArgInfo h r o v

class LensArgInfo a where
  getArgInfo :: a -> ArgInfo
  setArgInfo :: ArgInfo -> a -> a
  setArgInfo ai = mapArgInfo (const ai)
  mapArgInfo :: (ArgInfo -> ArgInfo) -> a -> a
  mapArgInfo f a = setArgInfo (f $ getArgInfo a) a

instance LensArgInfo ArgInfo where
  getArgInfo = id
  setArgInfo = const
  mapArgInfo = id

instance NFData ArgInfo where
  rnf (ArgInfo a b c d) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d

instance LensHiding ArgInfo where
  getHiding = argInfoHiding
  setHiding h ai = ai { argInfoHiding = h }
  mapHiding f ai = ai { argInfoHiding = f (argInfoHiding ai) }

instance LensRelevance ArgInfo where
  getRelevance = argInfoRelevance
  setRelevance h ai = ai { argInfoRelevance = h }
  mapRelevance f ai = ai { argInfoRelevance = f (argInfoRelevance ai) }

instance LensOrigin ArgInfo where
  getOrigin = argInfoOrigin
  setOrigin o ai = ai { argInfoOrigin = o }
  mapOrigin f ai = ai { argInfoOrigin = f (argInfoOrigin ai) }

defaultArgInfo :: ArgInfo
defaultArgInfo =  ArgInfo { argInfoHiding       = NotHidden
                          , argInfoRelevance    = Relevant
                          , argInfoOrigin       = UserWritten
                          , argInfoOverlappable = False }


---------------------------------------------------------------------------
-- * Arguments
---------------------------------------------------------------------------

data Arg e  = Arg
  { argInfo :: ArgInfo
  , unArg :: e
  } deriving (Typeable, Ord, Functor, Foldable, Traversable)

instance Decoration Arg where
  traverseF f (Arg ai a) = Arg ai <$> f a

instance HasRange a => HasRange (Arg a) where
    getRange = getRange . unArg

instance SetRange a => SetRange (Arg a) where
  setRange r = fmap $ setRange r

instance KillRange a => KillRange (Arg a) where
  killRange (Arg info a) = killRange2 Arg info a

instance Eq a => Eq (Arg a) where
  Arg (ArgInfo h1 _ _ _) x1 == Arg (ArgInfo h2 _ _ _) x2 = (h1, x1) == (h2, x2)

instance Show a => Show (Arg a) where
    show (Arg (ArgInfo h r o v) x) = showR r $ showO o $ showH h $ show x
      where
        showH Hidden     s = "{" ++ s ++ "}"
        showH NotHidden  s = "(" ++ s ++ ")"
        showH Instance   s = (if v then "overlap " else "") ++ "{{" ++ s ++ "}}"
        showR r s = case r of
          Irrelevant   -> "." ++ s
          NonStrict    -> "?" ++ s
          Forced Big   -> "!b" ++ s
          Forced Small -> "!" ++ s
          Relevant     -> "r" ++ s -- Andreas: I want to see it explicitly
        showO o s = case o of
          UserWritten -> "u" ++ s
          Inserted    -> "i" ++ s
          Reflected   -> "g" ++ s -- generated by reflection

instance NFData e => NFData (Arg e) where
  rnf (Arg a b) = rnf a `seq` rnf b

instance LensHiding (Arg e) where
  getHiding = getHiding . argInfo
  mapHiding = mapArgInfo . mapHiding

instance LensRelevance (Arg e) where
  getRelevance = getRelevance . argInfo
  mapRelevance = mapArgInfo . mapRelevance

instance LensOrigin (Arg e) where
  getOrigin = getOrigin . argInfo
  mapOrigin = mapArgInfo . mapOrigin

instance LensArgInfo (Arg a) where
  getArgInfo        = argInfo
  mapArgInfo f arg  = arg { argInfo = f $ argInfo arg }

defaultArg :: a -> Arg a
defaultArg = Arg defaultArgInfo

-- | @xs \`withArgsFrom\` args@ translates @xs@ into a list of 'Arg's,
-- using the elements in @args@ to fill in the non-'unArg' fields.
--
-- Precondition: The two lists should have equal length.

withArgsFrom :: [a] -> [Arg b] -> [Arg a]
xs `withArgsFrom` args =
  zipWith (\x arg -> fmap (const x) arg) xs args

withNamedArgsFrom :: [a] -> [NamedArg b] -> [NamedArg a]
xs `withNamedArgsFrom` args =
  zipWith (\x -> fmap (x <$)) xs args

---------------------------------------------------------------------------
-- * Names
---------------------------------------------------------------------------

class Eq a => Underscore a where
  underscore   :: a
  isUnderscore :: a -> Bool
  isUnderscore = (== underscore)

instance Underscore String where
  underscore = "_"

instance Underscore ByteString where
  underscore = ByteString.pack underscore

instance Underscore Doc where
  underscore = text underscore

---------------------------------------------------------------------------
-- * Function type domain
---------------------------------------------------------------------------

-- | Similar to 'Arg', but we need to distinguish
--   an irrelevance annotation in a function domain
--   (the domain itself is not irrelevant!)
--   from an irrelevant argument.
--
--   @Dom@ is used in 'Pi' of internal syntax, in 'Context' and 'Telescope'.
--   'Arg' is used for actual arguments ('Var', 'Con', 'Def' etc.)
--   and in 'Abstract' syntax and other situations.
data Dom e = Dom
  { domInfo   :: ArgInfo
  , unDom     :: e
  } deriving (Typeable, Ord, Functor, Foldable, Traversable)

instance Decoration Dom where
  traverseF f (Dom ai a) = Dom ai <$> f a

instance HasRange a => HasRange (Dom a) where
  getRange = getRange . unDom

instance KillRange a => KillRange (Dom a) where
  killRange (Dom info a) = killRange2 Dom info a

instance Eq a => Eq (Dom a) where
  Dom (ArgInfo h1 r1 _ _) x1 == Dom (ArgInfo h2 r2 _ _) x2 =
    (h1, ignoreForced r1, x1) == (h2, ignoreForced r2, x2)

instance Show a => Show (Dom a) where
  show = show . argFromDom

instance LensHiding (Dom e) where
  getHiding = getHiding . domInfo
  mapHiding = mapArgInfo . mapHiding

instance LensRelevance (Dom e) where
  getRelevance = getRelevance . domInfo
  mapRelevance = mapArgInfo . mapRelevance

instance LensArgInfo (Dom e) where
  getArgInfo = domInfo
  mapArgInfo f arg = arg { domInfo = f $ domInfo arg }

instance LensOrigin (Dom e) where
  getOrigin = getOrigin . getArgInfo
  mapOrigin = mapArgInfo . mapOrigin

argFromDom :: Dom a -> Arg a
argFromDom (Dom i a) = Arg i a

domFromArg :: Arg a -> Dom a
domFromArg (Arg i a) = Dom i a

defaultDom :: a -> Dom a
defaultDom = Dom defaultArgInfo

---------------------------------------------------------------------------
-- * Named arguments
---------------------------------------------------------------------------

-- | Something potentially carrying a name.
data Named name a =
    Named { nameOf     :: Maybe name
          , namedThing :: a
          }
    deriving (Eq, Ord, Typeable, Functor, Foldable, Traversable)

-- | Standard naming.
type Named_ = Named RString

unnamed :: a -> Named name a
unnamed = Named Nothing

named :: name -> a -> Named name a
named = Named . Just

instance Decoration (Named name) where
  traverseF f (Named n a) = Named n <$> f a

instance HasRange a => HasRange (Named name a) where
    getRange = getRange . namedThing

instance SetRange a => SetRange (Named name a) where
  setRange r = fmap $ setRange r

instance (KillRange name, KillRange a) => KillRange (Named name a) where
  killRange (Named n a) = Named (killRange n) (killRange a)

instance Show a => Show (Named_ a) where
    show (Named Nothing x)  = show x
    show (Named (Just n) x) = rawNameToString (rangedThing n) ++ " = " ++ show x

instance (NFData name, NFData a) => NFData (Named name a) where
  rnf (Named a b) = rnf a `seq` rnf b

-- | Only 'Hidden' arguments can have names.
type NamedArg a = Arg (Named_ a)

-- | Get the content of a 'NamedArg'.
namedArg :: NamedArg a -> a
namedArg = namedThing . unArg

defaultNamedArg :: a -> NamedArg a
defaultNamedArg = defaultArg . unnamed

-- | The functor instance for 'NamedArg' would be ambiguous,
--   so we give it another name here.
updateNamedArg :: (a -> b) -> NamedArg a -> NamedArg b
updateNamedArg = fmap . fmap

-- | @setNamedArg a b = updateNamedArg (const b) a@
setNamedArg :: NamedArg a -> b -> NamedArg b
setNamedArg a b = (b <$) <$> a

---------------------------------------------------------------------------
-- * Range decoration.
---------------------------------------------------------------------------

-- | Thing with range info.
data Ranged a = Ranged
  { rangeOf     :: Range
  , rangedThing :: a
  }
  deriving (Typeable, Functor, Foldable, Traversable)

-- | Thing with no range info.
unranged :: a -> Ranged a
unranged = Ranged noRange

instance Show a => Show (Ranged a) where
  show = show . rangedThing

instance Eq a => Eq (Ranged a) where
  Ranged _ x == Ranged _ y = x == y

instance Ord a => Ord (Ranged a) where
  compare (Ranged _ x) (Ranged _ y) = compare x y

instance HasRange (Ranged a) where
  getRange = rangeOf

instance KillRange (Ranged a) where
  killRange (Ranged _ x) = Ranged noRange x

instance Decoration Ranged where
  traverseF f (Ranged r x) = Ranged r <$> f x

-- | Ranges are not forced.

instance NFData a => NFData (Ranged a) where
  rnf (Ranged _ a) = rnf a

---------------------------------------------------------------------------
-- * Raw names (before parsing into name parts).
---------------------------------------------------------------------------

-- | A @RawName@ is some sort of string.
type RawName = String

rawNameToString :: RawName -> String
rawNameToString = id

stringToRawName :: String -> RawName
stringToRawName = id

-- | String with range info.
type RString = Ranged RawName

---------------------------------------------------------------------------
-- * Further constructor and projection info
---------------------------------------------------------------------------

-- | Where does the 'ConP' or 'Con' come from?
data ConOrigin
  = ConOSystem  -- ^ Inserted by system or expanded from an implicit pattern.
  | ConOCon     -- ^ User wrote a constructor (pattern).
  | ConORec     -- ^ User wrote a record (pattern).
  deriving (Typeable, Show, Eq, Ord, Enum, Bounded)

instance KillRange ConOrigin where
  killRange = id

-- | Prefer user-written over system-inserted.
bestConInfo :: ConOrigin -> ConOrigin -> ConOrigin
bestConInfo ConOSystem o = o
bestConInfo o _ = o

-- | Where does a projection come from?
data ProjOrigin
  = ProjPrefix    -- ^ User wrote a prefix projection.
  | ProjPostfix   -- ^ User wrote a postfix projection.
  | ProjSystem    -- ^ Projection was generated by the system.
  deriving (Typeable, Show, Eq, Ord, Enum, Bounded)

instance KillRange ProjOrigin where
  killRange = id

---------------------------------------------------------------------------
-- * Infixity, access, abstract, etc.
---------------------------------------------------------------------------

-- | Functions can be defined in both infix and prefix style. See
--   'Agda.Syntax.Concrete.LHS'.
data IsInfix = InfixDef | PrefixDef
    deriving (Typeable, Show, Eq, Ord)

-- | Access modifier.
data Access
  = PrivateAccess Origin
      -- ^ Store the 'Origin' of the private block that lead to this qualifier.
      --   This is needed for more faithful printing of declarations.
  | PublicAccess
  | OnlyQualified  -- ^ Visible from outside, but not exported when opening the module
                             --   Used for qualified constructors.
    deriving (Typeable, Show, Eq, Ord)

instance NFData Access where
  rnf _ = ()

instance HasRange Access where
  getRange _ = noRange

instance KillRange Access where
  killRange = id

-- | Abstract or concrete
data IsAbstract = AbstractDef | ConcreteDef
    deriving (Typeable, Show, Eq, Ord)

instance KillRange IsAbstract where
  killRange = id

-- | Is this definition eligible for instance search?
data IsInstance = InstanceDef | NotInstanceDef
    deriving (Typeable, Show, Eq, Ord)

instance KillRange IsInstance where
  killRange = id

instance HasRange IsInstance where
  getRange _ = noRange

instance NFData IsInstance where
  rnf InstanceDef    = ()
  rnf NotInstanceDef = ()

-- | Is this a macro definition?
data IsMacro = MacroDef | NotMacroDef
  deriving (Typeable, Show, Eq, Ord)

instance KillRange IsMacro where killRange = id
instance HasRange  IsMacro where getRange _ = noRange

type Nat    = Int
type Arity  = Nat

---------------------------------------------------------------------------
-- * NameId
---------------------------------------------------------------------------

-- | The unique identifier of a name. Second argument is the top-level module
--   identifier.
data NameId = NameId {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word64
    deriving (Eq, Ord, Typeable, Generic)

instance KillRange NameId where
  killRange = id

instance Show NameId where
  show (NameId x i) = show x ++ "@" ++ show i

instance Enum NameId where
  succ (NameId n m)     = NameId (n + 1) m
  pred (NameId n m)     = NameId (n - 1) m
  toEnum n              = __IMPOSSIBLE__  -- should not be used
  fromEnum (NameId n _) = fromIntegral n

instance NFData NameId where
  rnf (NameId _ _) = ()

instance Hashable NameId where
  {-# INLINE hashWithSalt #-}
  hashWithSalt salt (NameId n m) = hashWithSalt salt (n, m)

---------------------------------------------------------------------------
-- * Meta variables
---------------------------------------------------------------------------

-- | A meta variable identifier is just a natural number.
--
newtype MetaId = MetaId { metaId :: Nat }
    deriving (Eq, Ord, Num, Real, Enum, Integral, Typeable)

instance Pretty MetaId where
  pretty (MetaId n) = text $ "_" ++ show n

-- | Show non-record version of this newtype.
instance Show MetaId where
  showsPrec p (MetaId n) = showParen (p > 0) $
    showString "MetaId " . shows n

instance NFData MetaId where
  rnf (MetaId x) = rnf x

newtype Constr a = Constr a

------------------------------------------------------------------------
-- * Placeholders (used to parse sections)
------------------------------------------------------------------------

-- | The position of a name part or underscore in a name.

data PositionInName
  = Beginning
    -- ^ The following underscore is at the beginning of the name:
    -- @_foo@.
  | Middle
    -- ^ The following underscore is in the middle of the name:
    -- @foo_bar@.
  | End
    -- ^ The following underscore is at the end of the name: @foo_@.
  deriving (Show, Eq, Ord)

-- | Placeholders are used to represent the underscores in a section.

data MaybePlaceholder e
  = Placeholder !PositionInName
  | NoPlaceholder !(Strict.Maybe PositionInName) e
    -- ^ The second argument is used only (but not always) for name
    -- parts other than underscores.
  deriving (Typeable, Eq, Ord, Functor, Foldable, Traversable, Show)

-- | An abbreviation: @noPlaceholder = 'NoPlaceholder'
-- 'Strict.Nothing'@.

noPlaceholder :: e -> MaybePlaceholder e
noPlaceholder = NoPlaceholder Strict.Nothing

instance HasRange a => HasRange (MaybePlaceholder a) where
  getRange Placeholder{}       = noRange
  getRange (NoPlaceholder _ e) = getRange e

instance KillRange a => KillRange (MaybePlaceholder a) where
  killRange p@Placeholder{}     = p
  killRange (NoPlaceholder p e) = killRange1 (NoPlaceholder p) e

instance NFData a => NFData (MaybePlaceholder a) where
  rnf (Placeholder _)     = ()
  rnf (NoPlaceholder _ a) = rnf a

---------------------------------------------------------------------------
-- * Interaction meta variables
---------------------------------------------------------------------------

newtype InteractionId = InteractionId { interactionId :: Nat }
    deriving (Eq,Ord,Num,Integral,Real,Enum)

instance Show InteractionId where
    show (InteractionId x) = "?" ++ show x

instance KillRange InteractionId where killRange = id

-----------------------------------------------------------------------------
-- * Import directive
-----------------------------------------------------------------------------

-- | The things you are allowed to say when you shuffle names between name
--   spaces (i.e. in @import@, @namespace@, or @open@ declarations).
data ImportDirective' a b = ImportDirective
  { importDirRange :: Range
  , using          :: Using' a b
  , hiding         :: [ImportedName' a b]
  , impRenaming    :: [Renaming' a b]
  , publicOpen     :: Bool -- ^ Only for @open@. Exports the opened names from the current module.
  }
  deriving (Typeable, Eq)

data Using' a b = UseEverything | Using [ImportedName' a b]
  deriving (Typeable, Eq)

instance Semigroup (Using' a b) where
  UseEverything <> u             = u
  u             <> UseEverything = u
  Using xs      <> Using ys      = Using (xs ++ ys)

instance Monoid (Using' a b) where
  mempty  = UseEverything
  mappend = (<>)

-- | Default is directive is @private@ (use everything, but do not export).
defaultImportDir :: ImportDirective' a b
defaultImportDir = ImportDirective noRange UseEverything [] [] False

isDefaultImportDir :: ImportDirective' a b -> Bool
isDefaultImportDir (ImportDirective _ UseEverything [] [] False) = True
isDefaultImportDir _                                             = False

-- | An imported name can be a module or a defined name
data ImportedName' a b
  = ImportedModule  b
  | ImportedName    a
  deriving (Typeable, Eq, Ord)

setImportedName :: ImportedName' a a -> a -> ImportedName' a a
setImportedName (ImportedName   x) y = ImportedName   y
setImportedName (ImportedModule x) y = ImportedModule y

instance (Show a, Show b) => Show (ImportedName' a b) where
  show (ImportedModule x) = "module " ++ show x
  show (ImportedName   x) = show x

data Renaming' a b = Renaming
  { renFrom    :: ImportedName' a b
    -- ^ Rename from this name.
  , renTo      :: ImportedName' a b
    -- ^ To this one.  Must be same kind as 'renFrom'.
  , renToRange :: Range
    -- ^ The range of the \"to\" keyword.  Retained for highlighting purposes.
  }
  deriving (Typeable, Eq)

-- ** HasRange instances

instance (HasRange a, HasRange b) => HasRange (ImportDirective' a b) where
  getRange = importDirRange

instance (HasRange a, HasRange b) => HasRange (Using' a b) where
  getRange (Using  xs) = getRange xs
  getRange UseEverything = noRange

instance (HasRange a, HasRange b) => HasRange (Renaming' a b) where
  getRange r = getRange (renFrom r, renTo r)

instance (HasRange a, HasRange b) => HasRange (ImportedName' a b) where
  getRange (ImportedName   x) = getRange x
  getRange (ImportedModule x) = getRange x

-- ** KillRange instances

instance (KillRange a, KillRange b) => KillRange (ImportDirective' a b) where
  killRange (ImportDirective _ u h r p) =
    killRange3 (\u h r -> ImportDirective noRange u h r p) u h r

instance (KillRange a, KillRange b) => KillRange (Using' a b) where
  killRange (Using  i) = killRange1 Using  i
  killRange UseEverything = UseEverything

instance (KillRange a, KillRange b) => KillRange (Renaming' a b) where
  killRange (Renaming i n _) = killRange2 (\i n -> Renaming i n noRange) i n

instance (KillRange a, KillRange b) => KillRange (ImportedName' a b) where
  killRange (ImportedModule n) = killRange1 ImportedModule n
  killRange (ImportedName   n) = killRange1 ImportedName   n

-- ** NFData instances

-- | Ranges are not forced.

instance (NFData a, NFData b) => NFData (ImportDirective' a b) where
  rnf (ImportDirective _ a b c _) = rnf a `seq` rnf b `seq` rnf c

instance (NFData a, NFData b) => NFData (Using' a b) where
  rnf UseEverything = ()
  rnf (Using a)     = rnf a

-- | Ranges are not forced.

instance (NFData a, NFData b) => NFData (Renaming' a b) where
  rnf (Renaming a b _) = rnf a `seq` rnf b

instance (NFData a, NFData b) => NFData (ImportedName' a b) where
  rnf (ImportedModule a) = rnf a
  rnf (ImportedName a)   = rnf a

-----------------------------------------------------------------------------
-- * Termination
-----------------------------------------------------------------------------

-- | Termination check? (Default = TerminationCheck).
data TerminationCheck m
  = TerminationCheck
    -- ^ Run the termination checker.
  | NoTerminationCheck
    -- ^ Skip termination checking (unsafe).
  | NonTerminating
    -- ^ Treat as non-terminating.
  | Terminating
    -- ^ Treat as terminating (unsafe).  Same effect as 'NoTerminationCheck'.
  | TerminationMeasure Range m
    -- ^ Skip termination checking but use measure instead.
    deriving (Typeable, Show, Eq, Functor)

instance KillRange m => KillRange (TerminationCheck m) where
  killRange (TerminationMeasure _ m) = TerminationMeasure noRange (killRange m)
  killRange t                        = t

instance NFData a => NFData (TerminationCheck a) where
  rnf TerminationCheck         = ()
  rnf NoTerminationCheck       = ()
  rnf NonTerminating           = ()
  rnf Terminating              = ()
  rnf (TerminationMeasure _ a) = rnf a

-----------------------------------------------------------------------------
-- * Positivity
-----------------------------------------------------------------------------

-- | Positivity check? (Default = True).
type PositivityCheck = Bool
