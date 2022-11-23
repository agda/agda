{-| Some common syntactic entities are defined in this module.
-}
module Agda.Syntax.Common
  ( module Agda.Syntax.Common
  , module Agda.Syntax.Common.KeywordRange
  , module Agda.Syntax.TopLevelModuleName.Boot
  , Induction(..)
  )
  where

import Agda.Syntax.TopLevelModuleName.Boot

import Prelude hiding (null)

import Control.DeepSeq
import Control.Arrow ((&&&))
import Control.Applicative ((<|>), liftA2)

import Data.Bifunctor
import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as ByteString
import qualified Data.Foldable as Fold
import Data.Function (on)
import Data.Hashable (Hashable(..))
import qualified Data.Strict.Maybe as Strict
import Data.Word
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Text (Text)

import GHC.Generics (Generic)

import Agda.Syntax.Common.Aspect (Induction(..))
import Agda.Syntax.Common.KeywordRange
import Agda.Syntax.Common.Pretty
import Agda.Syntax.Position

import Agda.Utils.BiMap (HasTag(..))
import Agda.Utils.Boolean (Boolean(fromBool), IsBool(toBool))
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List1  ( List1, pattern (:|), (<|) )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.PartialOrd
import Agda.Utils.POMonoid

import Agda.Utils.Impossible

-- | Number @>= 0@.
type Nat    = Int
type Arity  = Nat

-- | Number @>= 1@.
type Nat1   = Nat

---------------------------------------------------------------------------
-- * IsMain
---------------------------------------------------------------------------

data IsMain = IsMain | NotMain
  deriving (Eq, Show)

-- | Conjunctive semigroup ('NotMain' is absorbing).
instance Semigroup IsMain where
  NotMain <> _ = NotMain
  _       <> NotMain = NotMain
  IsMain  <> IsMain = IsMain

instance Monoid IsMain where
  mempty = IsMain
  mappend = (<>)

---------------------------------------------------------------------------
-- * File
---------------------------------------------------------------------------

data FileType = AgdaFileType | MdFileType | RstFileType | TexFileType | OrgFileType | TypstFileType | TreeFileType
  deriving (Eq, Ord, Show, Generic)

instance Pretty FileType where
  pretty = \case
    AgdaFileType -> "Agda"
    MdFileType   -> "Markdown"
    RstFileType  -> "ReStructedText"
    TexFileType  -> "LaTeX"
    OrgFileType  -> "org-mode"
    TypstFileType -> "Typst"
    TreeFileType -> "Forester"

instance NFData FileType

---------------------------------------------------------------------------
-- * Agda variants
---------------------------------------------------------------------------

-- | Variants of Cubical Agda.

data Cubical = CErased | CFull
    deriving (Eq, Show, Generic)

instance NFData Cubical

cubicalOptionString :: Cubical -> String
cubicalOptionString = \case
  CErased -> "--erased-cubical"
  CFull   -> "--cubical"

-- | Agda variants.
--
-- Only some variants are tracked.

data Language
  = WithoutK
  | WithK
  | Cubical Cubical
    deriving (Eq, Show, Generic)

instance KillRange Language where
  killRange = id

instance NFData Language

---------------------------------------------------------------------------
-- * Backends
---------------------------------------------------------------------------

type BackendName = Text

---------------------------------------------------------------------------
-- * Some enums
---------------------------------------------------------------------------

-- | Distinguish constructors from pattern synonyms.

data ConstructorOrPatternSynonym = IsConstructor | IsPatternSynonym
  deriving (Show, Generic, Enum, Bounded)

instance Pretty ConstructorOrPatternSynonym where
  pretty = \case
    IsConstructor    -> "constructor"
    IsPatternSynonym -> "pattern synonym"

instance NFData ConstructorOrPatternSynonym

-- | Distinguish parsing a DISPLAY pragma from an ordinary left hand side.

data DisplayLHS = YesDisplayLHS | NoDisplayLHS
  deriving (Eq, Show, Generic, Enum, Bounded)

instance Boolean DisplayLHS where
  fromBool = \case
    True -> YesDisplayLHS
    False -> NoDisplayLHS

instance IsBool DisplayLHS where
  toBool = \case
    YesDisplayLHS -> True
    NoDisplayLHS -> False

---------------------------------------------------------------------------
-- * Record Directives
---------------------------------------------------------------------------

data RecordDirectives' a = RecordDirectives
  { recInductive   :: Maybe (Ranged Induction)
  , recHasEta      :: Maybe (Ranged HasEta0)
  , recPattern     :: Maybe Range
  , recConstructor :: a
  } deriving (Functor, Show, Eq, Foldable, Traversable)

instance Null a => Null (RecordDirectives' a) where
  empty = emptyRecordDirectives
  null (RecordDirectives a b c d) = and [null a, null b, null c, null d]

emptyRecordDirectives :: Null a => RecordDirectives' a
emptyRecordDirectives = RecordDirectives empty empty empty empty

instance HasRange a => HasRange (RecordDirectives' a) where
  getRange (RecordDirectives a b c d) = getRange (a,b,c,d)

instance KillRange a => KillRange (RecordDirectives' a) where
  killRange (RecordDirectives a b c d) = killRangeN RecordDirectives a b c d

instance NFData a => NFData (RecordDirectives' a) where
  rnf (RecordDirectives a b c d) = c `seq` rnf (a, b, d)

---------------------------------------------------------------------------
-- * Eta-equality
---------------------------------------------------------------------------

-- | Does a record come with eta-equality?
data HasEta' a
  = YesEta
  | NoEta a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance HasRange a => HasRange (HasEta' a) where
  getRange = foldMap getRange

instance KillRange a => KillRange (HasEta' a) where
  killRange = fmap killRange

instance NFData a => NFData (HasEta' a) where
  rnf YesEta    = ()
  rnf (NoEta p) = rnf p

-- | Pattern and copattern matching is allowed in the presence of eta.
--
--   In the absence of eta, we have to choose whether we want to allow
--   matching on the constructor or copattern matching with the projections.
--   Having both leads to breakage of subject reduction (issue #4560).

type HasEta  = HasEta' PatternOrCopattern
type HasEta0 = HasEta' ()

-- | For a record without eta, which type of matching do we allow?
data PatternOrCopattern
  = PatternMatching
      -- ^ Can match on the record constructor.
  | CopatternMatching
      -- ^ Can copattern match using the projections. (Default.)
  deriving (Show, Eq, Ord, Enum, Bounded)

instance NFData PatternOrCopattern where
  rnf PatternMatching   = ()
  rnf CopatternMatching = ()

instance HasRange PatternOrCopattern where
  getRange _ = noRange

instance KillRange PatternOrCopattern where
  killRange = id

-- | Can we pattern match on the record constructor?
class PatternMatchingAllowed a where
  patternMatchingAllowed :: a -> Bool

instance PatternMatchingAllowed PatternOrCopattern where
  patternMatchingAllowed = (== PatternMatching)

instance PatternMatchingAllowed HasEta where
  patternMatchingAllowed = \case
    YesEta -> True
    NoEta p -> patternMatchingAllowed p


-- | Can we construct a record by copattern matching?
class CopatternMatchingAllowed a where
  copatternMatchingAllowed :: a -> Bool

instance CopatternMatchingAllowed PatternOrCopattern where
  copatternMatchingAllowed = (== CopatternMatching)

instance CopatternMatchingAllowed HasEta where
  copatternMatchingAllowed = \case
    YesEta -> True
    NoEta p -> copatternMatchingAllowed p

---------------------------------------------------------------------------
-- * Induction
---------------------------------------------------------------------------

instance Pretty Induction where
  pretty Inductive   = "inductive"
  pretty CoInductive = "coinductive"

instance HasRange Induction where
  getRange _ = noRange

instance KillRange Induction where
  killRange = id

instance PatternMatchingAllowed Induction where
  patternMatchingAllowed = (== Inductive)

---------------------------------------------------------------------------
-- * Overlapping instances
---------------------------------------------------------------------------

data Overlappable = YesOverlap | NoOverlap
  deriving (Show, Eq, Ord)

-- | Just for the 'Hiding' instance. Should never combine different
--   overlapping.
instance Semigroup Overlappable where
  NoOverlap  <> NoOverlap  = NoOverlap
  YesOverlap <> YesOverlap = YesOverlap
  _          <> _          = __IMPOSSIBLE__

instance Monoid Overlappable where
  mempty  = NoOverlap
  mappend = (<>)

instance NFData Overlappable where
  rnf NoOverlap  = ()
  rnf YesOverlap = ()

-- | The possible overlap modes for an instance, also used for instance candidates.
data OverlapMode
  = Overlappable
  -- ^ User-written OVERLAPPABLE pragma: this candidate can *be removed*
  -- by a more specific candidate.

  | Overlapping
  -- ^ User-written OVERLAPPING pragma: this candidate can *remove* a
  -- less specific candidate.

  | Overlaps
  -- ^ User-written OVERLAPS pragma: both overlappable and overlapping.

  | DefaultOverlap
  -- ^ No user-written overlap pragma. This instance can be overlapped
  -- by an OVERLAPPING instance, and it can overlap OVERLAPPABLE
  -- instances.

  | Incoherent
  -- ^ User-written INCOHERENT pragma: both overlappable and
  -- overlapping; and, if there are multiple candidates after all
  -- overlap has been handled, make an arbitrary choice.

  | FieldOverlap
  -- ^ Overlapping instances in record fields.
  deriving (Show, Eq, Ord, Enum, Bounded)

instance Pretty OverlapMode where
  pretty = \case
    Overlappable   -> "OVERLAPPABLE"
    Overlapping    -> "OVERLAPPING"
    Incoherent     -> "INCOHERENT"
    Overlaps       -> "OVERLAPS"
    FieldOverlap   -> "overlap"
    DefaultOverlap -> empty

instance KillRange OverlapMode where
  killRange = id

instance NFData OverlapMode where
  rnf = \case
    Overlappable   -> ()
    Overlapping    -> ()
    Overlaps       -> ()
    DefaultOverlap -> ()
    FieldOverlap   -> ()
    Incoherent     -> ()

class HasOverlapMode a where
  lensOverlapMode :: Lens' a OverlapMode

instance HasOverlapMode OverlapMode where
  lensOverlapMode = id

isIncoherent, isOverlappable, isOverlapping :: HasOverlapMode a => a -> Bool
isIncoherent x = case x ^. lensOverlapMode of
  Incoherent -> True
  _          -> False

isOverlappable x = case x ^. lensOverlapMode of
  Overlappable -> True
  Incoherent   -> True
  Overlaps     -> True
  _            -> False

isOverlapping x = case x ^. lensOverlapMode of
  Overlapping -> True
  Incoherent  -> True
  Overlaps    -> True
  _           -> False

---------------------------------------------------------------------------
-- * Hiding
---------------------------------------------------------------------------

data Hiding  = Hidden | Instance Overlappable | NotHidden
  deriving (Show, Eq, Ord)

instance Pretty Hiding where
  pretty = text . hidingToString

hidingToString :: Hiding -> String
hidingToString = \case
  Hidden     -> "hidden"
  NotHidden  -> "visible"
  Instance{} -> "instance"

instance Null Hiding where
  empty = NotHidden

-- | 'Hiding' is an idempotent partial monoid, with unit 'NotHidden'.
--   'Instance' and 'NotHidden' are incompatible.
instance Semigroup Hiding where
  NotHidden  <> h           = h
  h          <> NotHidden   = h
  Hidden     <> Hidden      = Hidden
  Instance o <> Instance o' = Instance (o <> o')
  _          <> _           = __IMPOSSIBLE__

instance Monoid Hiding where
  mempty = empty
  mappend = (<>)

instance HasRange Hiding where
  getRange _ = noRange

instance KillRange Hiding where
  killRange = id

instance NFData Hiding where
  rnf Hidden       = ()
  rnf (Instance o) = rnf o
  rnf NotHidden    = ()

-- | Decorating something with 'Hiding' information.
data WithHiding a = WithHiding
  { whHiding :: !Hiding
  , whThing  :: a
  }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

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
--   Minimal implementation: @getHiding@ and @mapHiding@ or @LensArgInfo@.
class LensHiding a where

  getHiding :: a -> Hiding

  setHiding :: Hiding -> a -> a
  setHiding h = mapHiding (const h)

  mapHiding :: (Hiding -> Hiding) -> a -> a

  default getHiding :: LensArgInfo a => a -> Hiding
  getHiding = argInfoHiding . getArgInfo

  default mapHiding :: LensArgInfo a => (Hiding -> Hiding) -> a -> a
  mapHiding f = mapArgInfo $ \ ai -> ai { argInfoHiding = f $ argInfoHiding ai }

instance LensHiding Hiding where
  getHiding = id
  setHiding = const
  mapHiding = id

instance LensHiding (WithHiding a) where
  getHiding   (WithHiding h _) = h
  setHiding h (WithHiding _ a) = WithHiding h a
  mapHiding f (WithHiding h a) = WithHiding (f h) a

instance LensHiding a => LensHiding (Named nm a) where
  getHiding = getHiding . namedThing
  setHiding = fmap . setHiding
  mapHiding = fmap . mapHiding

-- | Monoidal composition of 'Hiding' information in some data.
mergeHiding :: LensHiding a => WithHiding a -> a
mergeHiding (WithHiding h a) = mapHiding (mappend h) a

-- | 'NotHidden' arguments are @visible@.
visible :: LensHiding a => a -> Bool
visible a = getHiding a == NotHidden

-- | 'Instance' and 'Hidden' arguments are @notVisible@.
notVisible :: LensHiding a => a -> Bool
notVisible a = getHiding a /= NotHidden

-- | 'Hidden' arguments are @hidden@.
hidden :: LensHiding a => a -> Bool
hidden a = getHiding a == Hidden

hide :: LensHiding a => a -> a
hide = setHiding Hidden

hideOrKeepInstance :: LensHiding a => a -> a
hideOrKeepInstance x =
  case getHiding x of
    Hidden     -> x
    Instance{} -> x
    NotHidden  -> setHiding Hidden x

makeInstance :: LensHiding a => a -> a
makeInstance = makeInstance' NoOverlap

makeInstance' :: LensHiding a => Overlappable -> a -> a
makeInstance' o = setHiding (Instance o)

isYesOverlap :: LensHiding a => a -> Bool
isYesOverlap x =
  case getHiding x of
    Instance YesOverlap -> True
    _ -> False

isInstance :: LensHiding a => a -> Bool
isInstance x =
  case getHiding x of
    Instance{} -> True
    _          -> False

-- | Ignores 'Overlappable'.
sameHiding :: (LensHiding a, LensHiding b) => a -> b -> Bool
sameHiding x y =
  case (getHiding x, getHiding y) of
    (Instance{}, Instance{}) -> True
    (hx, hy)                 -> hx == hy

---------------------------------------------------------------------------
-- * Modalities
---------------------------------------------------------------------------

-- | Type wrapper to indicate additive monoid/semigroup context.
newtype UnderAddition t = UnderAddition t deriving (Show, Functor, Eq, Ord, PartialOrd)

instance Applicative UnderAddition where
  pure = UnderAddition
  (<*>) (UnderAddition f) (UnderAddition a) = pure (f a)

-- | Type wrapper to indicate composition or multiplicative monoid/semigroup context.
newtype UnderComposition t = UnderComposition t deriving (Show, Functor, Eq, Ord, PartialOrd)

instance Applicative UnderComposition where
  pure = UnderComposition
  (<*>) (UnderComposition f) (UnderComposition a) = pure (f a)

-- | We have a tuple of modalities, which might not be fully orthogonal.
--   For example, irrelevant stuff is also run-time irrelevant.
data Modality = Modality
  { modRelevance :: Relevance
      -- ^ Legacy irrelevance.
      --   See Pfenning, LiCS 2001; Abel, Vezzosi and Winterhalter, ICFP 2017.
  , modQuantity  :: Quantity
      -- ^ Cardinality / runtime erasure.
      --   See Conor McBride, I got plenty o' nutting, Wadlerfest 2016.
      --   See Bob Atkey, Syntax and Semantics of Quantitative Type Theory, LiCS 2018.
  , modCohesion :: Cohesion
      -- ^ Cohesion/what was in Agda-flat.
      --   see "Brouwer's fixed-point theorem in real-cohesive homotopy type theory" (arXiv:1509.07584)
      --   Currently only the comonad is implemented.
  , modPolarity :: PolarityModality
      -- ^ Polarity annotations (strictly positive, ...)
  } deriving (Eq, Ord, Show, Generic)

-- | Dominance ordering.
instance PartialOrd Modality where
  comparable (Modality r q c p) (Modality r' q' c' p') = comparable (r, (q, (c, p))) (r', (q', (c', p')))

-- | Pointwise composition.
instance Semigroup (UnderComposition Modality) where
  (<>) = liftA2 composeModality

-- | Pointwise composition unit.
instance Monoid (UnderComposition Modality) where
  mempty  = pure unitModality
  mappend = (<>)

instance POSemigroup (UnderComposition Modality) where
instance POMonoid (UnderComposition Modality) where

instance LeftClosedPOMonoid (UnderComposition Modality) where
  inverseCompose = liftA2 inverseComposeModality

-- | Pointwise addition.
instance Semigroup (UnderAddition Modality) where
  (<>) = liftA2 addModality

-- | Pointwise additive unit.
instance Monoid (UnderAddition Modality) where
  mempty  = pure zeroModality
  mappend = (<>)

instance POSemigroup (UnderAddition Modality) where
instance POMonoid (UnderAddition Modality) where

-- | @m `moreUsableModality` m'@ means that an @m@ can be used
--   where ever an @m'@ is required.

moreUsableModality :: Modality -> Modality -> Bool
moreUsableModality m m' = related m POLE m'

usableModality :: LensModality a => a -> Bool
usableModality a = usableRelevance m && usableQuantity m && usableCohesion m
  where m = getModality a

-- | Multiplicative monoid (standard monoid).
composeModality :: Modality -> Modality -> Modality
composeModality (Modality r q c p) (Modality r' q' c' p') =
    Modality (r `composeRelevance` r')
             (q `composeQuantity` q')
             (c `composeCohesion` c')
             (p `composePolarity` p')

-- | Compose with modality flag from the left.
--   This function is e.g. used to update the modality information
--   on pattern variables @a@ after a match against something of modality @q@.
applyModality :: LensModality a => Modality -> a -> a
applyModality m = mapModality (m `composeModality`)

-- | @inverseComposeModality r x@ returns the least modality @y@
--   such that forall @x@, @y@ we have
--   @x \`moreUsableModality\` (r \`composeModality\` y)@
--   iff
--   @(r \`inverseComposeModality\` x) \`moreUsableModality\` y@ (Galois connection).
inverseComposeModality :: Modality -> Modality -> Modality
inverseComposeModality (Modality r q c p) (Modality r' q' c' p') =
  Modality (r `inverseComposeRelevance` r')
           (q `inverseComposeQuantity`  q')
           (c `inverseComposeCohesion`  c')
           (p `inverseComposePolarity`  p')

-- | Left division by a 'Modality'.
--   Used e.g. to modify context when going into a @m@ argument.
--
-- Note that this function does not change quantities.
inverseApplyModalityButNotQuantity :: LensModality a => Modality -> a -> a
inverseApplyModalityButNotQuantity m =
  mapModality (m' `inverseComposeModality`)
  where
  m' = setQuantity (Quantity1 Q1Inferred) m

-- | 'Modality' forms a pointwise additive monoid.
addModality :: Modality -> Modality -> Modality
addModality (Modality r q c p) (Modality r' q' c' p') =
  Modality (addRelevance r r')
           (addQuantity  q q')
           (addCohesion  c c')
           (addPolarity  p p')

-- | Identity under addition
zeroModality :: Modality
zeroModality = Modality zeroRelevance zeroQuantity zeroCohesion zeroPolarity

-- | Identity under composition
unitModality :: Modality
unitModality = Modality unitRelevance unitQuantity unitCohesion unitPolarity

-- | Absorptive element under addition.
topModality :: Modality
topModality = Modality topRelevance topQuantity topCohesion topPolarity

-- | The default Modality
--   Beware that this is neither the additive unit nor the unit under
--   composition, because the default quantity is ω.
defaultModality :: Modality
defaultModality = Modality defaultRelevance defaultQuantity defaultCohesion defaultPolarity

-- | Extract the positional modality component for checks regarding only them.
positionalModalityComponent :: Modality -> Modality
positionalModalityComponent m =
  defaultModality {modCohesion = modCohesion m}

-- | Equality ignoring origin.

sameModality :: (LensModality a, LensModality b) => a -> b -> Bool
sameModality x y = case (getModality x , getModality y) of
  (Modality r q c p , Modality r' q' c' p') -> sameRelevance r r' && sameQuantity q q' && sameCohesion c c' && samePolarity p p'

instance Null Modality where
  empty = defaultModality
  null (Modality r q c p) = and [ null r, null q, null c, null p ]

-- boilerplate instances

instance HasRange Modality where
  getRange (Modality r q c p) = getRange (r, q, c, p)

instance KillRange Modality where
  killRange (Modality r q c p) = killRangeN Modality r q c p

instance NFData Modality where

-- Lens stuff

lModRelevance :: Lens' Modality Relevance
lModRelevance f m = f (modRelevance m) <&> \ r -> m { modRelevance = r }

lModQuantity :: Lens' Modality Quantity
lModQuantity f m = f (modQuantity m) <&> \ q -> m { modQuantity = q }

lModCohesion :: Lens' Modality Cohesion
lModCohesion f m = f (modCohesion m) <&> \ q -> m { modCohesion = q }

lModPolarity :: Lens' Modality PolarityModality
lModPolarity f m = f (modPolarity m) <&> \ p -> m { modPolarity = p }

class LensModality a where

  getModality :: a -> Modality

  setModality :: Modality -> a -> a
  setModality = mapModality . const

  mapModality :: (Modality -> Modality) -> a -> a

  default getModality :: LensArgInfo a => a -> Modality
  getModality = argInfoModality . getArgInfo

  default mapModality :: LensArgInfo a => (Modality -> Modality) -> a -> a
  mapModality f = mapArgInfo $ \ ai -> ai { argInfoModality = f $ argInfoModality ai }

instance LensModality Modality where
  getModality = id
  setModality = const
  mapModality = id

instance LensRelevance Modality where
  getRelevance = modRelevance
  setRelevance h m = m { modRelevance = h }
  mapRelevance f m = m { modRelevance = f (modRelevance m) }

instance LensQuantity Modality where
  getQuantity = modQuantity
  setQuantity h m = m { modQuantity = h }
  mapQuantity f m = m { modQuantity = f (modQuantity m) }

instance LensCohesion Modality where
  getCohesion = modCohesion
  setCohesion h m = m { modCohesion = h }
  mapCohesion f m = m { modCohesion = f (modCohesion m) }

instance LensModalPolarity Modality where
  getModalPolarity = modPolarity
  setModalPolarity h m = m { modPolarity = h }
  mapModalPolarity f m = m { modPolarity = f (modPolarity m) }

-- default accessors for Relevance

getRelevanceMod :: LensModality a => LensGet a Relevance
getRelevanceMod = getRelevance . getModality

setRelevanceMod :: LensModality a => LensSet a Relevance
setRelevanceMod = mapModality . setRelevance

mapRelevanceMod :: LensModality a => LensMap a Relevance
mapRelevanceMod = mapModality . mapRelevance

-- default accessors for Quantity

getQuantityMod :: LensModality a => LensGet a Quantity
getQuantityMod = getQuantity . getModality

setQuantityMod :: LensModality a => LensSet a Quantity
setQuantityMod = mapModality . setQuantity

mapQuantityMod :: LensModality a => LensMap a Quantity
mapQuantityMod = mapModality . mapQuantity

-- default accessors for Cohesion

getCohesionMod :: LensModality a => LensGet a Cohesion
getCohesionMod = getCohesion . getModality

setCohesionMod :: LensModality a => LensSet a Cohesion
setCohesionMod = mapModality . setCohesion

mapCohesionMod :: LensModality a => LensMap a Cohesion
mapCohesionMod = mapModality . mapCohesion

-- default accessors for Polarity

getPolarityMod :: LensModality a => LensGet a PolarityModality
getPolarityMod = getModalPolarity . getModality

setPolarityMod :: LensModality a => LensSet a PolarityModality
setPolarityMod = mapModality . setModalPolarity

mapPolarityMod :: LensModality a => LensMap a PolarityModality
mapPolarityMod = mapModality . mapModalPolarity

---------------------------------------------------------------------------
-- * Quantities
---------------------------------------------------------------------------

-- ** Quantity origin.

-- | Origin of 'Quantity0'.
data Q0Origin
  = Q0Inferred       -- ^ User wrote nothing.
  | Q0       Range   -- ^ User wrote "@0".
  | Q0Erased Range   -- ^ User wrote "@erased".
  deriving (Show, Generic, Eq, Ord)

-- | Origin of 'Quantity1'.
data Q1Origin
  = Q1Inferred       -- ^ User wrote nothing.
  | Q1       Range   -- ^ User wrote "@1".
  | Q1Linear Range   -- ^ User wrote "@linear".
  deriving (Show, Generic, Eq, Ord)

-- | Origin of 'Quantityω'.
data QωOrigin
  = QωInferred       -- ^ User wrote nothing.
  | Qω       Range   -- ^ User wrote "@ω".
  | QωPlenty Range   -- ^ User wrote "@plenty".
  deriving (Show, Generic, Eq, Ord)

-- *** Instances for 'Q0Origin'.

-- | Right-biased composition, because the left quantity
--   acts as context, and the right one as occurrence.
instance Semigroup Q0Origin where
  (<>) = curry $ \case
    (Q0Inferred, o) -> o
    (o, Q0Inferred) -> o
    (o, Q0       r) -> Q0 $ fuseRange o r
    (o, Q0Erased r) -> Q0 $ fuseRange o r

instance Monoid Q0Origin where
  mempty = Q0Inferred
  mappend = (<>)

instance Null Q0Origin where
  empty = mempty

instance HasRange Q0Origin where
  getRange = \case
    Q0Inferred -> noRange
    Q0       r -> r
    Q0Erased r -> r

instance SetRange Q0Origin where
  setRange r = \case
    Q0Inferred -> Q0Inferred
    Q0       _ -> Q0       r
    Q0Erased _ -> Q0Erased r

instance KillRange Q0Origin where
  killRange = \case
    Q0Inferred -> Q0Inferred
    Q0       _ -> Q0       noRange
    Q0Erased _ -> Q0Erased noRange

instance NFData Q0Origin where
  rnf = \case
    Q0Inferred -> ()
    Q0       _ -> ()
    Q0Erased _ -> ()

-- *** Instances for 'Q1Origin'.

-- | Right-biased composition, because the left quantity
--   acts as context, and the right one as occurrence.
instance Semigroup Q1Origin where
  (<>) = curry $ \case
    (Q1Inferred, o) -> o
    (o, Q1Inferred) -> o
    (o, Q1       r) -> Q1 $ fuseRange o r
    (o, Q1Linear r) -> Q1 $ fuseRange o r

instance Monoid Q1Origin where
  mempty = Q1Inferred
  mappend = (<>)

instance Null Q1Origin where
  empty = mempty

instance HasRange Q1Origin where
  getRange = \case
    Q1Inferred -> noRange
    Q1       r -> r
    Q1Linear r -> r

instance SetRange Q1Origin where
  setRange r = \case
    Q1Inferred -> Q1Inferred
    Q1       _ -> Q1       r
    Q1Linear _ -> Q1Linear r

instance KillRange Q1Origin where
  killRange = \case
    Q1Inferred -> Q1Inferred
    Q1       _ -> Q1       noRange
    Q1Linear _ -> Q1Linear noRange

instance NFData Q1Origin where
  rnf = \case
    Q1Inferred -> ()
    Q1       _ -> ()
    Q1Linear _ -> ()

-- *** Instances for 'QωOrigin'.

-- | Right-biased composition, because the left quantity
--   acts as context, and the right one as occurrence.
instance Semigroup QωOrigin where
  (<>) = curry $ \case
    (QωInferred, o) -> o
    (o, QωInferred) -> o
    (o, Qω       r) -> Qω $ fuseRange o r
    (o, QωPlenty r) -> Qω $ fuseRange o r

instance Monoid QωOrigin where
  mempty = QωInferred
  mappend = (<>)

instance Null QωOrigin where
  empty = mempty

instance HasRange QωOrigin where
  getRange = \case
    QωInferred -> noRange
    Qω       r -> r
    QωPlenty r -> r

instance SetRange QωOrigin where
  setRange r = \case
    QωInferred -> QωInferred
    Qω       _ -> Qω       r
    QωPlenty _ -> QωPlenty r

instance KillRange QωOrigin where
  killRange = \case
    QωInferred -> QωInferred
    Qω       _ -> Qω       noRange
    QωPlenty _ -> QωPlenty noRange

instance NFData QωOrigin where
  rnf = \case
    QωInferred -> ()
    Qω       _ -> ()
    QωPlenty _ -> ()

-- ** Quantity.

-- | Quantity for linearity.
--
--   A quantity is a set of natural numbers, indicating possible semantic
--   uses of a variable.  A singleton set @{n}@ requires that the
--   corresponding variable is used exactly @n@ times.
--
data Quantity
  = Quantity0 Q0Origin -- ^ Zero uses @{0}@, erased at runtime.
  | Quantity1 Q1Origin -- ^ Linear use @{1}@ (could be updated destructively).
    -- Mostly TODO (needs postponable constraints between quantities to compute uses).
  | Quantityω QωOrigin -- ^ Unrestricted use @ℕ@.
  deriving (Show, Generic, Eq, Ord)
    -- @Ord@ instance in case @Quantity@ is used in keys for maps etc.

-- | Equality ignoring origin.

sameQuantity :: Quantity -> Quantity -> Bool
sameQuantity = curry $ \case
  (Quantity0{}, Quantity0{}) -> True
  (Quantity1{}, Quantity1{}) -> True
  (Quantityω{}, Quantityω{}) -> True
  _ -> False

-- | Composition of quantities (multiplication).
--
-- 'Quantity0' is dominant.
-- 'Quantity1' is neutral.
--
-- Right-biased for origin.
--
instance Semigroup (UnderComposition Quantity) where
  (<>) = liftA2 composeQuantity

-- | In the absense of finite quantities besides 0, ω is the unit.
--   Otherwise, 1 is the unit.
instance Monoid (UnderComposition Quantity) where
  mempty  = pure unitQuantity
  mappend = (<>)

instance POSemigroup (UnderComposition Quantity) where
instance POMonoid (UnderComposition Quantity) where

instance LeftClosedPOMonoid (UnderComposition Quantity) where
  inverseCompose = liftA2 inverseComposeQuantity

instance Semigroup (UnderAddition Quantity) where
  (<>) = liftA2 addQuantity

instance Monoid (UnderAddition Quantity) where
  mempty  = pure zeroQuantity
  mappend = (<>)

instance POSemigroup (UnderAddition Quantity) where
instance POMonoid (UnderAddition Quantity) where

-- | Note that the order is @ω ≤ 0,1@, more options is smaller.
instance PartialOrd Quantity where
  comparable = curry $ \case
    (q, q') | sameQuantity q q' -> POEQ
    -- ω is least
    (Quantityω{}, _)  -> POLT
    (_, Quantityω{})  -> POGT
    -- others are uncomparable
    _ -> POAny

-- | 'Quantity' forms an additive monoid with zero Quantity0.
addQuantity :: Quantity -> Quantity -> Quantity
addQuantity = curry $ \case
  -- ω is absorptive
  (q@Quantityω{}, _) -> q
  (_, q@Quantityω{}) -> q
  -- 0 is neutral
  (Quantity0{}, q) -> q
  (q, Quantity0{}) -> q
  -- 1 + 1 = ω
  (Quantity1 _, Quantity1 _) -> topQuantity

-- | Identity element under addition
zeroQuantity :: Quantity
zeroQuantity = Quantity0 mempty

-- | Absorptive element!
--   This differs from Relevance and Cohesion whose default
--   is the multiplicative unit.
defaultQuantity :: Quantity
defaultQuantity = topQuantity

-- | Identity element under composition
unitQuantity :: Quantity
unitQuantity = Quantityω mempty

-- | Absorptive element is ω.
topQuantity :: Quantity
topQuantity = Quantityω mempty

instance Null Quantity where
  empty = defaultQuantity
  null = hasQuantityω

-- | @m `moreUsableQuantity` m'@ means that an @m@ can be used
--   where ever an @m'@ is required.

moreQuantity :: Quantity -> Quantity -> Bool
moreQuantity m m' = related m POLE m'

-- | Composition of quantities (multiplication).
--
-- 'Quantity0' is dominant.
-- 'Quantity1' is neutral.
--
-- Right-biased for origin.
--
composeQuantity :: Quantity -> Quantity -> Quantity
composeQuantity = curry $ \case
  (Quantity1 o, Quantity1 o') -> Quantity1 (o <> o')
  (Quantity1{}, q           ) -> q
  (q          , Quantity1{} ) -> q
  (Quantity0 o, Quantity0 o') -> Quantity0 (o <> o')
  (_          , Quantity0 o ) -> Quantity0 o
  (Quantity0 o, _           ) -> Quantity0 o
  (Quantityω o, Quantityω o') -> Quantityω (o <> o')

-- | Compose with quantity flag from the left.
--   This function is e.g. used to update the quantity information
--   on pattern variables @a@ after a match against something of quantity @q@.

applyQuantity :: LensQuantity a => Quantity -> a -> a
applyQuantity q = mapQuantity (q `composeQuantity`)

-- | @inverseComposeQuantity r x@ returns the least quantity @y@
--   such that forall @x@, @y@ we have
--   @x \`moreQuantity\` (r \`composeQuantity\` y)@
--   iff
--   @(r \`inverseComposeQuantity\` x) \`moreQuantity\` y@ (Galois connection).

inverseComposeQuantity :: Quantity -> Quantity -> Quantity
inverseComposeQuantity = curry $ \case
    (Quantity1{} , x)              -> x             -- going to linear arg: nothing changes
    (Quantity0{} , x)              -> topQuantity   -- going to erased arg: every thing usable
    (Quantityω{} , x@Quantityω{})  -> x
    (Quantityω{} , _)              -> zeroQuantity  -- linear resources are unusable as arguments to unrestricted functions

-- | Left division by a 'Quantity'.
--   Used e.g. to modify context when going into a @q@ argument.

inverseApplyQuantity :: LensQuantity a => Quantity -> a -> a
inverseApplyQuantity q = mapQuantity (q `inverseComposeQuantity`)

-- | Check for 'Quantity0'.

hasQuantity0 :: LensQuantity a => a -> Bool
hasQuantity0 a
  | Quantity0{} <- getQuantity a = True
  | otherwise = False

-- | Check for 'Quantity1'.

hasQuantity1 :: LensQuantity a => a -> Bool
hasQuantity1 a
  | Quantity1{} <- getQuantity a = True
  | otherwise = False

-- | Check for 'Quantityω'.

hasQuantityω :: LensQuantity a => a -> Bool
hasQuantityω a
  | Quantityω{} <- getQuantity a = True
  | otherwise = False

-- | Did the user supply a quantity annotation?

noUserQuantity :: LensQuantity a => a -> Bool
noUserQuantity a = case getQuantity a of
  Quantity0 o -> null o
  Quantity1 o -> null o
  Quantityω o -> null o

-- | A thing of quantity 0 is unusable, all others are usable.

usableQuantity :: LensQuantity a => a -> Bool
usableQuantity = not . hasQuantity0

-- boilerplate instances

class LensQuantity a where

  getQuantity :: a -> Quantity

  setQuantity :: Quantity -> a -> a
  setQuantity = mapQuantity . const

  mapQuantity :: (Quantity -> Quantity) -> a -> a

  default getQuantity :: LensModality a => a -> Quantity
  getQuantity = modQuantity . getModality

  default mapQuantity :: LensModality a => (Quantity -> Quantity) -> a -> a
  mapQuantity f = mapModality $ \ ai -> ai { modQuantity = f $ modQuantity ai }

instance LensQuantity Quantity where
  getQuantity = id
  setQuantity = const
  mapQuantity = id

instance HasRange Quantity where
  getRange = \case
    Quantity0 o -> getRange o
    Quantity1 o -> getRange o
    Quantityω o -> getRange o

instance SetRange Quantity where
  setRange r = \case
    Quantity0 o -> Quantity0 $ setRange r o
    Quantity1 o -> Quantity1 $ setRange r o
    Quantityω o -> Quantityω $ setRange r o

instance KillRange Quantity where
  killRange = \case
    Quantity0 o -> Quantity0 $ killRange o
    Quantity1 o -> Quantity1 $ killRange o
    Quantityω o -> Quantityω $ killRange o

instance NFData Quantity where
  rnf (Quantity0 o) = rnf o
  rnf (Quantity1 o) = rnf o
  rnf (Quantityω o) = rnf o

isQuantity0 :: LensQuantity a => a -> Bool
isQuantity0 a = case getQuantity a of
  Quantity0{} -> True
  _ -> False

isQuantityω :: LensQuantity a => a -> Bool
isQuantityω a = case getQuantity a of
  Quantityω{} -> True
  _ -> False

-- ** Erased.

-- | A special case of 'Quantity': erased or not.
--
-- Note that the 'Ord' instance does *not* ignore the origin
-- arguments.

data Erased
  = Erased Q0Origin
  | NotErased QωOrigin
  deriving (Show, Eq, Ord, Generic)

-- | The default value of type 'Erased': not erased.

defaultErased :: Erased
defaultErased = NotErased QωInferred

-- | 'Erased' can be embedded into 'Quantity'.

asQuantity :: Erased -> Quantity
asQuantity (Erased    o) = Quantity0 o
asQuantity (NotErased o) = Quantityω o

-- | 'Quantity' can be projected onto 'Erased'.

erasedFromQuantity :: Quantity -> Maybe Erased
erasedFromQuantity = \case
  Quantity1{} -> Nothing
  Quantity0 o -> Just $ Erased    o
  Quantityω o -> Just $ NotErased o

-- | Equality ignoring origin.

sameErased :: Erased -> Erased -> Bool
sameErased = sameQuantity `on` asQuantity

-- | Is the value \"erased\"?

isErased :: Erased -> Bool
isErased = hasQuantity0 . asQuantity

instance NFData Erased

instance HasRange Erased where
  getRange = getRange . asQuantity

instance KillRange Erased where
  killRange = \case
    Erased o    -> Erased $ killRange o
    NotErased o -> NotErased $ killRange o

-- | Composition of values of type 'Erased'.
--
-- 'Erased' is dominant.
-- 'NotErased' is neutral.
--
-- Right-biased for the origin.

composeErased :: Erased -> Erased -> Erased
composeErased = curry $ \case
  (Erased o,    Erased o')    -> Erased (o <> o')
  (NotErased _, Erased o)     -> Erased o
  (Erased o,    NotErased _)  -> Erased o
  (NotErased o, NotErased o') -> NotErased (o <> o')

instance Semigroup (UnderComposition Erased) where
  (<>) = liftA2 composeErased

---------------------------------------------------------------------------
-- * Relevance
---------------------------------------------------------------------------

-- ** Relevance origin

-- | Origin of 'Relevant'.

data OriginRelevant
  = ORelInferred        -- ^ User wrote nothing.
  | ORelRelevant Range  -- ^ User wrote "@relevant".
  deriving (Show, Generic)

-- | Origin of 'Irrelevant'.

data OriginIrrelevant
  = OIrrInferred          -- ^ User wrote nothing.
  | OIrrDot        Range  -- ^ User wrote ".".
  | OIrrIrr        Range  -- ^ User wrote "@irr".
  | OIrrIrrelevant Range  -- ^ User wrote "@irrelevant".
  deriving (Show, Generic)

-- | Origin of 'ShapeIrrelevant'.

data OriginShapeIrrelevant
  = OShIrrInferred               -- ^ User wrote nothing.
  | OShIrrDotDot          Range  -- ^ User wrote "..".
  | OShIrrShIrr           Range  -- ^ User wrote "@shirr".
  | OShIrrShapeIrrelevant Range  -- ^ User wrote "@shape-irrelevant".
  deriving (Show, Generic)

-- *** Instances for 'OriginRelevant'

instance Null OriginRelevant where
  empty = ORelInferred
  null = \case
    ORelInferred -> True
    _ -> False

instance Semigroup OriginRelevant where
  (<>) = curry \case
    (ORelInferred, o  ) -> o
    (o, ORelInferred  ) -> o
    (o, ORelRelevant r) -> ORelRelevant $ fuseRange o r

instance Monoid OriginRelevant where
  mempty = empty

instance HasRange OriginRelevant where
  getRange = \case
    ORelInferred   -> noRange
    ORelRelevant r -> r

instance SetRange OriginRelevant where
  setRange r = \case
    ORelInferred   -> ORelInferred
    ORelRelevant _ -> ORelRelevant r

instance KillRange OriginRelevant where
  killRange = setRange noRange

instance NFData OriginRelevant where
  rnf = \case
    ORelInferred   -> ()
    ORelRelevant _ -> ()

-- *** Instances for 'OriginIrrelevant'

instance Null OriginIrrelevant where
  empty = OIrrInferred
  null = \case
    OIrrInferred -> True
    _ -> False

-- | Right-biased composition, because the left relevance
--   acts as context, and the right one as occurrence.

instance Semigroup OriginIrrelevant where
  (<>) = curry \case
    (OIrrInferred, o    ) -> o
    (o, OIrrInferred    ) -> o
    (o, OIrrDot        r) -> OIrrDot        $ fuseRange o r
    (o, OIrrIrr        r) -> OIrrIrr        $ fuseRange o r
    (o, OIrrIrrelevant r) -> OIrrIrrelevant $ fuseRange o r

instance Monoid OriginIrrelevant where
  mempty = empty

instance HasRange OriginIrrelevant where
  getRange = \case
    OIrrInferred     -> noRange
    OIrrDot        r -> r
    OIrrIrr        r -> r
    OIrrIrrelevant r -> r

instance SetRange OriginIrrelevant where
  setRange r = \case
    OIrrInferred     -> OIrrInferred
    OIrrDot _        -> OIrrDot r
    OIrrIrr _        -> OIrrIrr r
    OIrrIrrelevant _ -> OIrrIrrelevant r

instance KillRange OriginIrrelevant where
  killRange = setRange noRange

instance NFData OriginIrrelevant where
  rnf = \case
    OIrrInferred     -> ()
    OIrrDot _        -> ()
    OIrrIrr _        -> ()
    OIrrIrrelevant _ -> ()

-- *** Instances for 'OriginShapeIrrelevant'

instance Null OriginShapeIrrelevant where
  empty = OShIrrInferred
  null = \case
    OShIrrInferred -> True
    _ -> False

-- | Right-biased composition, because the left relevance
--   acts as context, and the right one as occurrence.

instance Semigroup OriginShapeIrrelevant where
  (<>) = curry \case
    (OShIrrInferred, o         ) -> o
    (o, OShIrrInferred         ) -> o
    (o, OShIrrDotDot          r) -> OShIrrDotDot          $ fuseRange o r
    (o, OShIrrShIrr           r) -> OShIrrShIrr           $ fuseRange o r
    (o, OShIrrShapeIrrelevant r) -> OShIrrShapeIrrelevant $ fuseRange o r

instance Monoid OriginShapeIrrelevant where
  mempty = empty

instance HasRange OriginShapeIrrelevant where
  getRange = \case
    OShIrrInferred          -> noRange
    OShIrrDotDot          r -> r
    OShIrrShIrr           r -> r
    OShIrrShapeIrrelevant r -> r

instance SetRange OriginShapeIrrelevant where
  setRange r = \case
    OShIrrInferred          -> OShIrrInferred
    OShIrrDotDot _          -> OShIrrDotDot r
    OShIrrShIrr _           -> OShIrrShIrr r
    OShIrrShapeIrrelevant _ -> OShIrrShapeIrrelevant r

instance KillRange OriginShapeIrrelevant where
  killRange = setRange noRange

instance NFData OriginShapeIrrelevant where
  rnf = \case
    OShIrrInferred          -> ()
    OShIrrDotDot _          -> ()
    OShIrrShIrr _           -> ()
    OShIrrShapeIrrelevant _ -> ()

-- ** Relevance levels

-- | A function argument can be relevant or irrelevant.
--   See "Agda.TypeChecking.Irrelevance".
data Relevance
  = Relevant OriginRelevant
      -- ^ The argument is (possibly) relevant at compile-time.
  | ShapeIrrelevant OriginShapeIrrelevant
      -- ^ Like 'Quantity0', the argument may never flow into evaluation position.
      --   So it is irrelevant at run-time,
      --   yet treated relevantly during equality checking.
      --
      --   Unlike 'Quantity0', it is used to type 'Irrelevant' arguments in functions:
      --   If you enable @--experimental-irrelevance@,
      --   then the type of an irrelevant function is forced to be shape-irrelevant.
      --   See:
      --   - <https://doi.org/10.2168/LMCS-8(1:29)2012> example 2.8
      --     (Not enforcing shape-irrelevant codomains can break subject reduction!)
      --   - <https://dl.acm.org/doi/10.1145/3110277>
      --   - <https://doi.org/10.1145/3209108.3209119>
  | Irrelevant OriginIrrelevant
      -- ^ The argument is irrelevant at compile- and runtime.
    deriving (Show, Generic)

instance Eq Relevance where
  (==) = sameRelevance

instance HasRange Relevance where
  getRange = \case
    Relevant        o -> getRange o
    ShapeIrrelevant o -> getRange o
    Irrelevant      o -> getRange o

instance SetRange Relevance where
  setRange r = \case
    Relevant        o -> Relevant        $ setRange r o
    ShapeIrrelevant o -> ShapeIrrelevant $ setRange r o
    Irrelevant      o -> Irrelevant      $ setRange r o

instance KillRange Relevance where
  killRange = setRange noRange

instance NFData Relevance where
  rnf = \case
    Relevant        o -> rnf o
    ShapeIrrelevant o -> rnf o
    Irrelevant      o -> rnf o

-- | A lens to access the 'Relevance' attribute in data structures.
--   Minimal implementation: @getRelevance@ and @mapRelevance@ or @LensModality@.
class LensRelevance a where

  getRelevance :: a -> Relevance

  setRelevance :: Relevance -> a -> a
  setRelevance h = mapRelevance (const h)

  mapRelevance :: (Relevance -> Relevance) -> a -> a

  default getRelevance :: LensModality a => a -> Relevance
  getRelevance = modRelevance . getModality

  default mapRelevance :: LensModality a => (Relevance -> Relevance) -> a -> a
  mapRelevance f = mapModality $ \ ai -> ai { modRelevance = f $ modRelevance ai }

instance LensRelevance Relevance where
  getRelevance = id
  setRelevance = const
  mapRelevance = id

relevant :: Relevance
relevant = Relevant empty

irrelevant :: Relevance
irrelevant = Irrelevant empty

shapeIrrelevant :: Relevance
shapeIrrelevant = ShapeIrrelevant empty

isRelevant :: LensRelevance a => a -> Bool
isRelevant a = case getRelevance a of
  Relevant{} -> True
  _ -> False

isIrrelevant :: LensRelevance a => a -> Bool
isIrrelevant a = case getRelevance a of
  Irrelevant{} -> True
  _ -> False

isShapeIrrelevant :: LensRelevance a => a -> Bool
isShapeIrrelevant a = case getRelevance a of
  ShapeIrrelevant{} -> True
  _ -> False

-- | Information ordering.
-- @Relevant  \`moreRelevant\`
--  ShapeIrrelevant \`moreRelevant\`
--  Irrelevant@
moreRelevant :: Relevance -> Relevance -> Bool
moreRelevant = (<=)

-- | Equality ignoring origin.
sameRelevance :: Relevance -> Relevance -> Bool
sameRelevance = curry $ \case
  (Relevant        {}, Relevant        {}) -> True
  (Irrelevant      {}, Irrelevant      {}) -> True
  (ShapeIrrelevant {}, ShapeIrrelevant {}) -> True
  _ -> False

-- | More relevant is smaller.
instance Ord Relevance where
  compare = curry \case
    (r, r') | sameRelevance r r' -> EQ
    -- top
    (_, Irrelevant{}) -> LT
    (Irrelevant{}, _) -> GT
    -- bottom
    (Relevant{}, _) -> LT
    (_, Relevant{}) -> GT
    -- redundant case
    (ShapeIrrelevant{}, ShapeIrrelevant{}) -> EQ

-- | More relevant is smaller.
instance PartialOrd Relevance where
  comparable = comparableOrd

-- | @usableRelevance rel == False@ iff we cannot use a variable of @rel@.
usableRelevance :: LensRelevance a => a -> Bool
usableRelevance = isRelevant

-- | 'Relevance' composition.
--   'Irrelevant' is dominant, 'Relevant' is neutral.
--   Composition coincides with 'max'.
composeRelevance :: Relevance -> Relevance -> Relevance
composeRelevance = curry \case
  (Relevant o        , Relevant o'       ) -> Relevant (o <> o')
  (Relevant{}        , r                 ) -> r
  (r                 , Relevant{}        ) -> r
  (Irrelevant o      , Irrelevant o'     ) -> Irrelevant (o <> o')
  (_                 , Irrelevant o      ) -> Irrelevant o
  (Irrelevant o      , _                 ) -> Irrelevant o
  (ShapeIrrelevant o , ShapeIrrelevant o') -> ShapeIrrelevant (o <> o')

-- | Compose with relevance flag from the left.
--   This function is e.g. used to update the relevance information
--   on pattern variables @a@ after a match against something @rel@.
applyRelevance :: LensRelevance a => Relevance -> a -> a
applyRelevance rel = mapRelevance (rel `composeRelevance`)

-- | @inverseComposeRelevance r x@ returns the most irrelevant @y@
--   such that forall @x@, @y@ we have
--   @x \`moreRelevant\` (r \`composeRelevance\` y)@
--   iff
--   @(r \`inverseComposeRelevance\` x) \`moreRelevant\` y@ (Galois connection).
inverseComposeRelevance :: Relevance -> Relevance -> Relevance
inverseComposeRelevance = curry \case
  (_                 , Relevant o       ) -> Relevant o   -- can't get more relevant
  (Relevant{}        , x                ) -> x            -- going to relevant arg.: nothing changes
                                                          -- because Relevant is comp.-neutral
  (Irrelevant{}      , x                ) -> relevant     -- going irrelevant: every thing usable
  (ShapeIrrelevant{} , Irrelevant o     ) -> Irrelevant o -- otherwise: irrelevant things remain unusable
  (ShapeIrrelevant{} , ShapeIrrelevant{}) -> relevant     -- but @ShapeIrrelevant@s become usable

-- | Left division by a 'Relevance'.
--   Used e.g. to modify context when going into a @rel@ argument.
inverseApplyRelevance :: LensRelevance a => Relevance -> a -> a
inverseApplyRelevance rel = mapRelevance (rel `inverseComposeRelevance`)

-- | 'Relevance' forms a semigroup under composition.
instance Semigroup (UnderComposition Relevance) where
  (<>) = liftA2 composeRelevance

-- | 'Relevant' is the unit under composition.
instance Monoid (UnderComposition Relevance) where
  mempty  = pure unitRelevance
  mappend = (<>)

instance POSemigroup (UnderComposition Relevance) where
instance POMonoid (UnderComposition Relevance) where

instance LeftClosedPOMonoid (UnderComposition Relevance) where
  inverseCompose = liftA2 inverseComposeRelevance

instance Semigroup (UnderAddition Relevance) where
  (<>) = liftA2 addRelevance

instance Monoid (UnderAddition Relevance) where
  mempty  = pure zeroRelevance
  mappend = (<>)

instance POSemigroup (UnderAddition Relevance) where
instance POMonoid (UnderAddition Relevance) where

-- | Combine inferred 'Relevance'.
--   The unit is 'Irrelevant'.
addRelevance :: Relevance -> Relevance -> Relevance
addRelevance = min

-- | 'Relevance' forms a monoid under addition, and even a semiring.
zeroRelevance :: Relevance
zeroRelevance = irrelevant

-- | Identity element under composition
unitRelevance :: Relevance
unitRelevance = relevant

-- | Absorptive element under addition.
topRelevance :: Relevance
topRelevance = relevant

-- | Default Relevance is the identity element under composition
defaultRelevance :: Relevance
defaultRelevance = unitRelevance

instance Null Relevance where
  empty = defaultRelevance
  null = isRelevant

-- | Irrelevant function arguments may appear non-strictly in the codomain type.
irrelevantToShapeIrrelevant :: Relevance -> Relevance
irrelevantToShapeIrrelevant Irrelevant{} = shapeIrrelevant
irrelevantToShapeIrrelevant rel = rel

-- | Applied when working on types (unless --experimental-irrelevance).
shapeIrrelevantToRelevant :: Relevance -> Relevance
shapeIrrelevantToRelevant ShapeIrrelevant{} = relevant
shapeIrrelevantToRelevant rel = rel

shapeIrrelevantToIrrelevant :: Relevance -> Relevance
shapeIrrelevantToIrrelevant ShapeIrrelevant{} = irrelevant
shapeIrrelevantToIrrelevant rel = rel

---------------------------------------------------------------------------
-- * Annotations
---------------------------------------------------------------------------

-- | We have a tuple of annotations, which might not be fully orthogonal.
data Annotation = Annotation
  { annLock :: Lock
    -- ^ Fitch-style dependent right adjoints.
    --   See Modal Dependent Type Theory and Dependent Right Adjoints, arXiv:1804.05236.
  } deriving (Eq, Ord, Show, Generic)

instance HasRange Annotation where
  getRange _ = noRange

instance KillRange Annotation where
  killRange = id

defaultAnnotation :: Annotation
defaultAnnotation = Annotation defaultLock

instance Null Annotation where
  empty = defaultAnnotation
  null (Annotation lock) = null lock

instance NFData Annotation where
  rnf (Annotation l) = rnf l

class LensAnnotation a where

  getAnnotation :: a -> Annotation

  setAnnotation :: Annotation -> a -> a

  mapAnnotation :: (Annotation -> Annotation) -> a -> a
  mapAnnotation f a = setAnnotation (f $ getAnnotation a) a

  default getAnnotation :: LensArgInfo a => a -> Annotation
  getAnnotation = argInfoAnnotation . getArgInfo

  default setAnnotation :: LensArgInfo a => Annotation -> a -> a
  setAnnotation a = mapArgInfo $ \ ai -> ai { argInfoAnnotation = a }

instance LensAnnotation Annotation where
  getAnnotation = id
  setAnnotation = const
  mapAnnotation = id

instance LensAnnotation (Arg t) where
  getAnnotation = getAnnotation . getArgInfo
  setAnnotation = mapArgInfo . setAnnotation


---------------------------------------------------------------------------
-- * Locks
---------------------------------------------------------------------------

data LockOrigin
  = LockOLock -- ^ The user wrote @lock.
  | LockOTick -- ^ The user wrote @tick.
  deriving (Show, Generic, Eq, Enum, Bounded, Ord)

data Lock
  = IsNotLock
  | IsLock LockOrigin
  -- ^ In the future there might be different kinds of them.
  --   For now we assume lock weakening.
  deriving (Show, Generic, Eq, Ord)

defaultLock :: Lock
defaultLock = IsNotLock

instance Null Lock where
  empty = defaultLock

instance NFData Lock where
  rnf IsNotLock          = ()
  rnf (IsLock LockOLock) = ()
  rnf (IsLock LockOTick) = ()

class LensLock a where

  getLock :: a -> Lock

  setLock :: Lock -> a -> a
  setLock = mapLock . const

  mapLock :: (Lock -> Lock) -> a -> a
  mapLock f a = setLock (f $ getLock a) a

instance LensLock Lock where
  getLock = id
  setLock = const
  mapLock = id

instance LensLock ArgInfo where
  getLock = annLock . argInfoAnnotation
  setLock l info = info { argInfoAnnotation = (argInfoAnnotation info){ annLock = l } }

instance LensLock (Arg t) where
  getLock = getLock . getArgInfo
  setLock = mapArgInfo . setLock

---------------------------------------------------------------------------
-- * Cohesion
---------------------------------------------------------------------------

-- | Cohesion modalities
--   see "Brouwer's fixed-point theorem in real-cohesive homotopy type theory" (arXiv:1509.07584)
--   types are now given an additional topological layer which the modalities interact with.
data Cohesion
  = Flat        -- ^ same points, discrete topology, idempotent comonad, box-like.
  | Continuous  -- ^ identity modality.
  -- | Sharp    -- ^ same points, codiscrete topology, idempotent monad, diamond-like.
  | Squash      -- ^ single point space, artificially added for Flat left-composition.
    deriving (Show, Eq, Enum, Bounded, Generic)

allCohesions :: [Cohesion]
allCohesions = [minBound..maxBound]

instance HasRange Cohesion where
  getRange _ = noRange

instance SetRange Cohesion where
  setRange _ = id

instance KillRange Cohesion where
  killRange rel = rel -- no range to kill

instance NFData Cohesion where
  rnf Flat       = ()
  rnf Continuous = ()
  rnf Squash     = ()

-- | A lens to access the 'Cohesion' attribute in data structures.
--   Minimal implementation: @getCohesion@ and @mapCohesion@ or @LensModality@.
class LensCohesion a where

  getCohesion :: a -> Cohesion

  setCohesion :: Cohesion -> a -> a
  setCohesion h = mapCohesion (const h)

  mapCohesion :: (Cohesion -> Cohesion) -> a -> a

  default getCohesion :: LensModality a => a -> Cohesion
  getCohesion = modCohesion . getModality

  default mapCohesion :: LensModality a => (Cohesion -> Cohesion) -> a -> a
  mapCohesion f = mapModality $ \ ai -> ai { modCohesion = f $ modCohesion ai }

instance LensCohesion Cohesion where
  getCohesion = id
  setCohesion = const
  mapCohesion = id

isContinuous :: LensCohesion a => a -> Bool
isContinuous = (Continuous ==) . getCohesion

-- | Information ordering.
-- @Flat  \`moreCohesion\`
--  Continuous \`moreCohesion\`
--  Sharp \`moreCohesion\`
--  Squash@
moreCohesion :: Cohesion -> Cohesion -> Bool
moreCohesion = (<=)

-- | Equality ignoring origin.
sameCohesion :: Cohesion -> Cohesion -> Bool
sameCohesion = (==)

-- | Order is given by implication: flatter is smaller.
instance Ord Cohesion where
  compare = curry $ \case
    (r, r') | r == r' -> EQ
    -- top
    (_, Squash) -> LT
    (Squash, _) -> GT
    -- bottom
    (Flat, _) -> LT
    (_, Flat) -> GT
    -- redundant case
    (Continuous,Continuous) -> EQ

-- | Flatter is smaller.
instance PartialOrd Cohesion where
  comparable = comparableOrd

-- | @usableCohesion rel == False@ iff we cannot use a variable of @rel@.
usableCohesion :: LensCohesion a => a -> Bool
usableCohesion a = getCohesion a `moreCohesion` Continuous

-- | 'Cohesion' composition.
--   'Squash' is dominant, 'Continuous' is neutral.
composeCohesion :: Cohesion -> Cohesion -> Cohesion
composeCohesion r r' =
  case (r, r') of
    (Squash, _) -> Squash
    (_, Squash) -> Squash
    (Flat, _)  -> Flat
    (_, Flat)  -> Flat
    (Continuous, Continuous) -> Continuous

-- | Compose with cohesion flag from the left.
--   This function is e.g. used to update the cohesion information
--   on pattern variables @a@ after a match against something of cohesion @rel@.
applyCohesion :: LensCohesion a => Cohesion -> a -> a
applyCohesion rel = mapCohesion (rel `composeCohesion`)

-- | @inverseComposeCohesion r x@ returns the least @y@
--   such that forall @x@, @y@ we have
--   @x \`moreCohesion\` (r \`composeCohesion\` y)@
--   iff
--   @(r \`inverseComposeCohesion\` x) \`moreCohesion\` y@ (Galois connection).
--   The above law fails for @r = Squash@.
inverseComposeCohesion :: Cohesion -> Cohesion -> Cohesion
inverseComposeCohesion r x =
  case (r, x) of
    (Continuous  , x) -> x          -- going to continous arg.: nothing changes
                                    -- because Continuous is comp.-neutral
    (Squash, x)       -> Flat       -- in squash position everything is usable
    (Flat , Flat)     -> Flat       -- otherwise: Flat things remain Flat
    (Flat , _)        -> Squash     -- but everything else becomes unusable.

-- | Left division by a 'Cohesion'.
--   Used e.g. to modify context when going into a @rel@ argument.
inverseApplyCohesion :: LensCohesion a => Cohesion -> a -> a
inverseApplyCohesion rel = mapCohesion (rel `inverseComposeCohesion`)

-- | 'Cohesion' forms a semigroup under composition.
instance Semigroup (UnderComposition Cohesion) where
  (<>) = liftA2 composeCohesion

-- | 'Continous' is the multiplicative unit.
instance Monoid (UnderComposition Cohesion) where
  mempty  = pure unitCohesion
  mappend = (<>)

instance POSemigroup (UnderComposition Cohesion) where
instance POMonoid (UnderComposition Cohesion) where

instance LeftClosedPOMonoid (UnderComposition Cohesion) where
  inverseCompose = liftA2 inverseComposeCohesion

-- | 'Cohesion' forms a semigroup under addition.
instance Semigroup (UnderAddition Cohesion) where
  (<>) = liftA2 addCohesion

-- | 'Squash' is the additive unit.
instance Monoid (UnderAddition Cohesion) where
  mempty  = pure zeroCohesion
  mappend = (<>)

instance POSemigroup (UnderAddition Cohesion) where
instance POMonoid (UnderAddition Cohesion) where

-- | Combine inferred 'Cohesion'.
--   The unit is 'Squash'.
addCohesion :: Cohesion -> Cohesion -> Cohesion
addCohesion = min

-- | 'Cohesion' forms a monoid under addition, and even a semiring.
zeroCohesion :: Cohesion
zeroCohesion = Squash

-- | Identity under composition
unitCohesion :: Cohesion
unitCohesion = Continuous

-- | Absorptive element under addition.
topCohesion :: Cohesion
topCohesion = Flat

-- | Default Cohesion is the identity element under composition
defaultCohesion :: Cohesion
defaultCohesion = unitCohesion

instance Null Cohesion where
  empty = defaultCohesion
  null = isContinuous

---------------------------------------------------------------------------
-- * Polarity
---------------------------------------------------------------------------

-- | The different polarity options
data ModalPolarity
  = UnusedPolarity    -- ^ argument will not be used.
  | StrictlyPositive  -- ^ argument will only be used in strictly positive position.
  | Positive          -- ^ argument will only be used in positive position.
  | Negative          -- ^ argument will only be used in negative position.
  | MixedPolarity     -- ^ we don't know anything, argument can be used anywhere.
    deriving (Show, Ord, Enum, Eq, Bounded, Generic)

allModalPolarities :: [ModalPolarity]
allModalPolarities = [minBound..maxBound]

-- | The derived Ord instance for ModalPolarity is just used for
--   serialisation and has no particular meaning. The actual order on
--   modalities is a partial order.
instance PartialOrd ModalPolarity where
  comparable x y | x == y = POEQ
  comparable _ UnusedPolarity = POLT
  comparable UnusedPolarity _ = POGT
  comparable _ MixedPolarity = POGT
  comparable MixedPolarity _ = POLT
  comparable _ Negative = POAny
  comparable Negative _ = POAny
  comparable Positive StrictlyPositive = POLT
  comparable StrictlyPositive Positive = POGT
  comparable _ _ = __IMPOSSIBLE__

-- | @morePolarity' x y@ is True whenever a variable of polarity x can be
--   used anywhere where a variable of polarity y is expected.
--   Note that @morePolarity' x y@ actually means x <= y.
morePolarity' :: ModalPolarity -> ModalPolarity -> Bool
morePolarity' x y = case comparable x y of
  POLT -> True
  POLE -> True
  POEQ -> True
  _    -> False

-- | 'ModalPolarity' composition.
--   'UnusedPolarity' is dominant, 'StrictlyPositive' is neutral.
composePolarity' :: ModalPolarity -> ModalPolarity -> ModalPolarity
composePolarity' p p' =
  case (p, p') of
    (UnusedPolarity, _)  -> UnusedPolarity
    (_, UnusedPolarity)  -> UnusedPolarity
    (MixedPolarity, _)   -> MixedPolarity
    (_, MixedPolarity)   -> MixedPolarity
    (Negative, Negative) -> Positive
    (Negative, _) -> Negative
    (_, Negative) -> Negative
    (StrictlyPositive, StrictlyPositive) -> StrictlyPositive
    (_, _) -> Positive

-- | @inverseComposePolarity r x@ returns the least @y@
--   such that forall @x@, @y@ we have
--   @x \`morePolarity'\` (r \`composePolarity\` y)@
--   iff
--   @(r \`inverseComposePolarity\` x) \`morePolarity'\` y@ (Galois connection).
inverseComposePolarity' :: ModalPolarity -> ModalPolarity -> ModalPolarity
inverseComposePolarity' p x =
  case (p, x) of
    (MixedPolarity, MixedPolarity) -> MixedPolarity
    (MixedPolarity, _) -> UnusedPolarity
    (StrictlyPositive , x) -> x
    (UnusedPolarity, _) -> MixedPolarity
    (Positive, StrictlyPositive) -> UnusedPolarity
    (Positive, x) -> x
    (Negative, Positive) -> Negative
    (Negative, Negative) -> Positive
    (Negative, MixedPolarity) -> MixedPolarity
    (Negative, _) -> UnusedPolarity

-- | Combine inferred 'ModalPolarity'.
--   The unit is 'UnusedPolarity'.
addPolarity' :: ModalPolarity -> ModalPolarity -> ModalPolarity
addPolarity' p p' = case (p, p') of
  (MixedPolarity, _) -> MixedPolarity
  (_, MixedPolarity) -> MixedPolarity
  (UnusedPolarity, x) -> x
  (x, UnusedPolarity) -> x
  (Negative, Negative) -> Negative
  (Negative, _) -> MixedPolarity
  (_, Negative) -> MixedPolarity
  (Positive, _) -> Positive
  (_, Positive) -> Positive
  (StrictlyPositive, StrictlyPositive) -> StrictlyPositive


data PolarityModality = PolarityModality
  { modPolarityAnn :: ModalPolarity    -- ^ The actual polarity of the variable
  , modPolarityOrigin :: ModalPolarity -- ^ The original polarity annotation by the user
  , modPolarityLock :: ModalPolarity   -- ^ The locks of the variable (= composition of all denominators the variable has been left divided by)
  } deriving (Show, Ord, Bounded, Generic)

instance Eq PolarityModality where
  (PolarityModality p o l) == (PolarityModality p' o' l') = p == p'

withStandardLock :: ModalPolarity -> PolarityModality
withStandardLock p = PolarityModality p p StrictlyPositive

instance HasRange PolarityModality where
  getRange _ = noRange

instance SetRange PolarityModality where
  setRange _ = id

instance KillRange PolarityModality where
  killRange rel = rel -- no range to kill

instance NFData PolarityModality where
  rnf (PolarityModality p o l) = ()

instance PartialOrd PolarityModality where
  comparable (PolarityModality p _ _) (PolarityModality p' _ _) = comparable p p'

-- | A lens to access the 'PolarityModality' attribute in data structures.
--   Minimal implementation: @getModalPolarity@ and @mapModalPolarity@ or @LensModality@.
class LensModalPolarity a where

  getModalPolarity :: a -> PolarityModality

  setModalPolarity :: PolarityModality -> a -> a
  setModalPolarity h = mapModalPolarity (const h)

  mapModalPolarity :: (PolarityModality -> PolarityModality) -> a -> a

  default getModalPolarity :: LensModality a => a -> PolarityModality
  getModalPolarity = modPolarity . getModality

  default mapModalPolarity :: LensModality a => (PolarityModality -> PolarityModality) -> a -> a
  mapModalPolarity f = mapModality $ \ ai -> ai { modPolarity = f $ modPolarity ai }

instance LensModalPolarity PolarityModality where
  getModalPolarity = id
  setModalPolarity = const
  mapModalPolarity = id

-- | Equality for polarities.
samePolarity :: PolarityModality -> PolarityModality -> Bool
samePolarity (PolarityModality p _ _) (PolarityModality p' _ _) = p == p'

morePolarity :: PolarityModality -> PolarityModality -> Bool
morePolarity (PolarityModality p _ _) (PolarityModality p' _ _) = morePolarity' p p'

-- | @usablePolarity pol == False@ iff we cannot use a variable of @pol@.
usablePolarity :: LensModalPolarity a => a -> Bool
usablePolarity a = modPolarityAnn pol `morePolarity'` StrictlyPositive
  where
    pol = getModalPolarity a

-- | 'PolarityModality' composition.
--
composePolarity :: PolarityModality -> PolarityModality -> PolarityModality
composePolarity (PolarityModality p o l) (PolarityModality p' o' l') =
  PolarityModality (composePolarity' p p') o' l'

-- | Compose with polarity flag from the left.
--   This function is e.g. used to update the polarity information
--   on pattern variables @a@ after a match against something of polarity @pol@.
applyPolarity :: LensModalPolarity a => PolarityModality -> a -> a
applyPolarity pol = mapModalPolarity (pol `composePolarity`)

-- | @inverseComposePolarity r x@ returns the least @y@
--   such that forall @x@, @y@ we have
--   @x \`morePolarity'\` (r \`composePolarity\` y)@
--   iff
--   @(r \`inverseComposePolarity\` x) \`morePolarity'\` y@ (Galois connection).
inverseComposePolarity :: PolarityModality -> PolarityModality -> PolarityModality
inverseComposePolarity (PolarityModality p o l) (PolarityModality p' o' l') =
  PolarityModality (inverseComposePolarity' p p') o' (composePolarity' l' p)

-- | Left division by a 'PolarityModality'.
--   Used e.g. to modify context when going into a @pol@ argument.
inverseApplyPolarity :: LensModalPolarity a => PolarityModality -> a -> a
inverseApplyPolarity pol = mapModalPolarity (pol `inverseComposePolarity`)

-- | 'ModalPolarity' forms a semigroup under composition.
instance Semigroup (UnderComposition PolarityModality) where
  (<>) = liftA2 composePolarity

-- | 'Continous' is the multiplicative unit.
instance Monoid (UnderComposition PolarityModality) where
  mempty  = pure unitPolarity
  mappend = (<>)

instance POSemigroup (UnderComposition PolarityModality) where
instance POMonoid (UnderComposition PolarityModality) where

instance LeftClosedPOMonoid (UnderComposition PolarityModality) where
  inverseCompose = liftA2 inverseComposePolarity

-- | 'ModalPolarity' forms a semigroup under addition.
instance Semigroup (UnderAddition PolarityModality) where
  (<>) = liftA2 addPolarity

-- | '' is the additive unit.
instance Monoid (UnderAddition PolarityModality) where
  mempty  = pure zeroPolarity
  mappend = (<>)

instance POSemigroup (UnderAddition PolarityModality) where
instance POMonoid (UnderAddition PolarityModality) where

-- | Combine inferred 'PolarityModality'.
--
addPolarity :: PolarityModality -> PolarityModality -> PolarityModality
addPolarity (PolarityModality p o l) (PolarityModality p' o' l') =
  PolarityModality (addPolarity' p p') o' l'

-- | 'ModalPolarity' forms a monoid under addition, and even a semiring.
zeroPolarity :: PolarityModality
zeroPolarity = withStandardLock UnusedPolarity

-- | Identity under composition
unitPolarity :: PolarityModality
unitPolarity = withStandardLock StrictlyPositive

-- | Alias for Negative polarity
negativePolarity :: PolarityModality
negativePolarity = withStandardLock Negative

-- | Absorptive element under addition.
topPolarity :: PolarityModality
topPolarity = withStandardLock MixedPolarity

-- | Default used when not caring about polarity
defaultPolarity :: PolarityModality
defaultPolarity = withStandardLock MixedPolarity

instance Null PolarityModality where
  empty = defaultPolarity

---------------------------------------------------------------------------
-- * Origin of arguments (user-written, inserted or reflected)
---------------------------------------------------------------------------

-- | Origin of arguments.
data Origin
  = UserWritten     -- ^ From the source file / user input.  (Preserve!)
  | Inserted        -- ^ E.g. inserted hidden arguments.
  | Reflected       -- ^ Produced by the reflection machinery.
  | CaseSplit       -- ^ Produced by an interactive case split.
  | Substitution    -- ^ Named application produced to represent a substitution. E.g. "?0 (x = n)" instead of "?0 n"
  | ExpandedPun     -- ^ An expanded hidden argument pun.
  | Generalization  -- ^ Inserted by the generalization process
  deriving (Show, Eq, Ord)

instance HasRange Origin where
  getRange _ = noRange

instance KillRange Origin where
  killRange = id

instance NFData Origin where
  rnf UserWritten = ()
  rnf Inserted = ()
  rnf Reflected = ()
  rnf CaseSplit = ()
  rnf Substitution = ()
  rnf ExpandedPun = ()
  rnf Generalization = ()

-- | Decorating something with 'Origin' information.
data WithOrigin a = WithOrigin
  { woOrigin :: !Origin
  , woThing  :: a
  }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Decoration WithOrigin where
  traverseF f (WithOrigin h a) = WithOrigin h <$> f a

instance Pretty a => Pretty (WithOrigin a) where
  prettyPrec p = prettyPrec p . woThing

instance HasRange a => HasRange (WithOrigin a) where
  getRange = getRange . dget

instance SetRange a => SetRange (WithOrigin a) where
  setRange = fmap . setRange

instance KillRange a => KillRange (WithOrigin a) where
  killRange = fmap killRange

instance NFData a => NFData (WithOrigin a) where
  rnf (WithOrigin _ a) = rnf a

-- | A lens to access the 'Origin' attribute in data structures.
--   Minimal implementation: @getOrigin@ and @mapOrigin@ or @LensArgInfo@.

class LensOrigin a where

  getOrigin :: a -> Origin

  setOrigin :: Origin -> a -> a
  setOrigin o = mapOrigin (const o)

  mapOrigin :: (Origin -> Origin) -> a -> a

  default getOrigin :: LensArgInfo a => a -> Origin
  getOrigin = argInfoOrigin . getArgInfo

  default mapOrigin :: LensArgInfo a => (Origin -> Origin) -> a -> a
  mapOrigin f = mapArgInfo $ \ ai -> ai { argInfoOrigin = f $ argInfoOrigin ai }

instance LensOrigin Origin where
  getOrigin = id
  setOrigin = const
  mapOrigin = id

instance LensOrigin (WithOrigin a) where
  getOrigin   (WithOrigin h _) = h
  setOrigin h (WithOrigin _ a) = WithOrigin h a
  mapOrigin f (WithOrigin h a) = WithOrigin (f h) a

-----------------------------------------------------------------------------
-- * Free variable annotations
-----------------------------------------------------------------------------

data FreeVariables = UnknownFVs | KnownFVs IntSet
  deriving (Eq, Ord, Show)

instance Semigroup FreeVariables where
  UnknownFVs   <> _            = UnknownFVs
  _            <> UnknownFVs   = UnknownFVs
  KnownFVs vs1 <> KnownFVs vs2 = KnownFVs (IntSet.union vs1 vs2)

instance Monoid FreeVariables where
  mempty  = KnownFVs IntSet.empty
  mappend = (<>)

instance KillRange FreeVariables where
  killRange = id

instance NFData FreeVariables where
  rnf UnknownFVs    = ()
  rnf (KnownFVs fv) = rnf fv

unknownFreeVariables :: FreeVariables
unknownFreeVariables = UnknownFVs

noFreeVariables :: FreeVariables
noFreeVariables = mempty

oneFreeVariable :: Int -> FreeVariables
oneFreeVariable = KnownFVs . IntSet.singleton

freeVariablesFromList :: [Int] -> FreeVariables
freeVariablesFromList = mconcat . map oneFreeVariable

-- | A lens to access the 'FreeVariables' attribute in data structures.
--   Minimal implementation: @getFreeVariables@ and @mapFreeVariables@ or @LensArgInfo@.
class LensFreeVariables a where

  getFreeVariables :: a -> FreeVariables

  setFreeVariables :: FreeVariables -> a -> a
  setFreeVariables o = mapFreeVariables (const o)

  mapFreeVariables :: (FreeVariables -> FreeVariables) -> a -> a

  default getFreeVariables :: LensArgInfo a => a -> FreeVariables
  getFreeVariables = argInfoFreeVariables . getArgInfo

  default mapFreeVariables :: LensArgInfo a => (FreeVariables -> FreeVariables) -> a -> a
  mapFreeVariables f = mapArgInfo $ \ ai -> ai { argInfoFreeVariables = f $ argInfoFreeVariables ai }

instance LensFreeVariables FreeVariables where
  getFreeVariables = id
  setFreeVariables = const
  mapFreeVariables = id

hasNoFreeVariables :: LensFreeVariables a => a -> Bool
hasNoFreeVariables x =
  case getFreeVariables x of
    UnknownFVs  -> False
    KnownFVs fv -> IntSet.null fv

---------------------------------------------------------------------------
-- * Argument decoration
---------------------------------------------------------------------------

-- | A function argument can be hidden and/or irrelevant.

data ArgInfo = ArgInfo
  { argInfoHiding        :: Hiding
  , argInfoModality      :: Modality
  , argInfoOrigin        :: Origin
  , argInfoFreeVariables :: FreeVariables
  , argInfoAnnotation    :: Annotation
    -- ^ Sometimes we want a different kind of binder/pi-type, without it
    --   supporting any of the @Modality@ interface.
  } deriving (Eq, Ord, Show)

instance HasRange ArgInfo where
  getRange (ArgInfo h m o _fv a) = getRange (h, m, o, a)

instance KillRange ArgInfo where
  killRange (ArgInfo h m o fv a) = killRangeN ArgInfo h m o fv a

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
  rnf (ArgInfo a b c d e) = rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e

instance LensHiding ArgInfo where
  getHiding = argInfoHiding
  setHiding h ai = ai { argInfoHiding = h }
  mapHiding f ai = ai { argInfoHiding = f (argInfoHiding ai) }

instance LensModality ArgInfo where
  getModality = argInfoModality
  setModality m ai = ai { argInfoModality = m }
  mapModality f ai = ai { argInfoModality = f (argInfoModality ai) }

instance LensOrigin ArgInfo where
  getOrigin = argInfoOrigin
  setOrigin o ai = ai { argInfoOrigin = o }
  mapOrigin f ai = ai { argInfoOrigin = f (argInfoOrigin ai) }

instance LensFreeVariables ArgInfo where
  getFreeVariables = argInfoFreeVariables
  setFreeVariables o ai = ai { argInfoFreeVariables = o }
  mapFreeVariables f ai = ai { argInfoFreeVariables = f (argInfoFreeVariables ai) }

instance LensAnnotation ArgInfo where
  getAnnotation = argInfoAnnotation
  setAnnotation m ai = ai { argInfoAnnotation = m }
  mapAnnotation f ai = ai { argInfoAnnotation = f (argInfoAnnotation ai) }

-- inherited instances

instance LensRelevance ArgInfo where
  getRelevance = getRelevanceMod
  setRelevance = setRelevanceMod
  mapRelevance = mapRelevanceMod

instance LensQuantity ArgInfo where
  getQuantity = getQuantityMod
  setQuantity = setQuantityMod
  mapQuantity = mapQuantityMod

instance LensCohesion ArgInfo where
  getCohesion = getCohesionMod
  setCohesion = setCohesionMod
  mapCohesion = mapCohesionMod

instance LensModalPolarity ArgInfo where
  getModalPolarity = getPolarityMod
  setModalPolarity = setPolarityMod
  mapModalPolarity = mapPolarityMod

instance Null ArgInfo where
  empty = defaultArgInfo
  null (ArgInfo h m _o _fv ann) = and [ null h, null m, null ann ]

defaultArgInfo :: ArgInfo
defaultArgInfo =  ArgInfo
  { argInfoHiding        = NotHidden
  , argInfoModality      = defaultModality
  , argInfoOrigin        = UserWritten
  , argInfoFreeVariables = UnknownFVs
  , argInfoAnnotation    = defaultAnnotation
  }

defaultIrrelevantArgInfo :: ArgInfo
defaultIrrelevantArgInfo = setRelevance irrelevant defaultArgInfo


-- Accessing through ArgInfo

-- default accessors for Hiding

getHidingArgInfo :: LensArgInfo a => LensGet a Hiding
getHidingArgInfo = getHiding . getArgInfo

setHidingArgInfo :: LensArgInfo a => LensSet a Hiding
setHidingArgInfo = mapArgInfo . setHiding

mapHidingArgInfo :: LensArgInfo a => LensMap a Hiding
mapHidingArgInfo = mapArgInfo . mapHiding

-- default accessors for Modality

getModalityArgInfo :: LensArgInfo a => LensGet a Modality
getModalityArgInfo = getModality . getArgInfo

setModalityArgInfo :: LensArgInfo a => LensSet a Modality
setModalityArgInfo = mapArgInfo . setModality

mapModalityArgInfo :: LensArgInfo a => LensMap a Modality
mapModalityArgInfo = mapArgInfo . mapModality

-- default accessors for Origin

getOriginArgInfo :: LensArgInfo a => LensGet a Origin
getOriginArgInfo = getOrigin . getArgInfo

setOriginArgInfo :: LensArgInfo a => LensSet a Origin
setOriginArgInfo = mapArgInfo . setOrigin

mapOriginArgInfo :: LensArgInfo a => LensMap a Origin
mapOriginArgInfo = mapArgInfo . mapOrigin

-- default accessors for FreeVariables

getFreeVariablesArgInfo :: LensArgInfo a => LensGet a FreeVariables
getFreeVariablesArgInfo = getFreeVariables . getArgInfo

setFreeVariablesArgInfo :: LensArgInfo a => LensSet a FreeVariables
setFreeVariablesArgInfo = mapArgInfo . setFreeVariables

mapFreeVariablesArgInfo :: LensArgInfo a => LensMap a FreeVariables
mapFreeVariablesArgInfo = mapArgInfo . mapFreeVariables

-- inserted hidden arguments

isInsertedHidden :: (LensHiding a, LensOrigin a) => a -> Bool
isInsertedHidden a = getHiding a == Hidden && getOrigin a == Inserted

---------------------------------------------------------------------------
-- * Arguments
---------------------------------------------------------------------------

data Arg e  = Arg
  { argInfo :: ArgInfo
  , unArg :: e
  } deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Decoration Arg where
  traverseF f (Arg ai a) = Arg ai <$> f a

instance HasRange a => HasRange (Arg a) where
    getRange = getRange . unArg

instance SetRange a => SetRange (Arg a) where
  setRange r = fmap $ setRange r

instance KillRange a => KillRange (Arg a) where
  killRange (Arg info a) = killRangeN Arg info a

-- Andreas, 2019-07-05, issue #3889
-- A dedicated equality for with-abstraction now exists,
-- thus, we can use intensional equality for Arg.
--
-- -- | Ignores 'Quantity', 'Relevance', 'Origin', and 'FreeVariables'.
-- --   Ignores content of argument if 'Irrelevant'.
-- --
-- instance Eq a => Eq (Arg a) where
--   Arg (ArgInfo h1 m1 _ _) x1 == Arg (ArgInfo h2 m2 _ _) x2 =
--     h1 == h2 && (isIrrelevant m1 || isIrrelevant m2 || x1 == x2)
--     -- Andreas, 2017-10-04, issue #2775, ignore irrelevant arguments during with-abstraction.
--     -- This is a hack, we should not use '(==)' in with-abstraction
--     -- and more generally not use it on Syntax.
--     -- Andrea: except for caching.

-- instance Show a => Show (Arg a) where
--     show (Arg (ArgInfo h (Modality r q) o fv) a) = showFVs fv $ showQ q $ showR r $ showO o $ showH h $ show a
--       where
--         showH Hidden       s = "{" ++ s ++ "}"
--         showH NotHidden    s = "(" ++ s ++ ")"
--         showH (Instance o) s = showOv o ++ "{{" ++ s ++ "}}"
--           where showOv YesOverlap = "overlap "
--                 showOv NoOverlap  = ""
--         showR r s = case r of
--           Irrelevant      -> "." ++ s
--           ShapeIrrelevant -> "?" ++ s
--           Relevant        -> "r" ++ s -- Andreas: I want to see it explicitly
--         showQ q s = case q of
--           Quantity0   -> "0" ++ s
--           Quantity1   -> "1" ++ s
--           Quantityω   -> "ω" ++ s
--         showO o s = case o of
--           UserWritten -> "u" ++ s
--           Inserted    -> "i" ++ s
--           Reflected   -> "g" ++ s -- generated by reflection
--           CaseSplit   -> "c" ++ s -- generated by case split
--           Substitution -> "s" ++ s
--         showFVs UnknownFVs    s = s
--         showFVs (KnownFVs fv) s = "fv" ++ show (IntSet.toList fv) ++ s

-- -- defined in Concrete.Pretty
-- instance Pretty a => Pretty (Arg a) where
--     pretty (Arg (ArgInfo h (Modality r q) o fv) a) = prettyFVs fv $ prettyQ q $ prettyR r $ prettyO o $ prettyH h $ pretty a
--       where
--         prettyH Hidden       s = "{" <> s <> "}"
--         prettyH NotHidden    s = "(" <> s <> ")"
--         prettyH (Instance o) s = prettyOv o <> "{{" <> s <> "}}"
--           where prettyOv YesOverlap = "overlap "
--                 prettyOv NoOverlap  = ""
--         prettyR r s = case r of
--           Irrelevant   -> "." <> s
--           ShapeIrrelevant    -> "?" <> s
--           Relevant     -> "r" <> s -- Andreas: I want to see it explicitly
--         prettyQ q s = case q of
--           Quantity0   -> "0" <> s
--           Quantity1   -> "1" <> s
--           Quantityω   -> "ω" <> s
--         prettyO o s = case o of
--           UserWritten -> "u" <> s
--           Inserted    -> "i" <> s
--           Reflected   -> "g" <> s -- generated by reflection
--           CaseSplit   -> "c" <> s -- generated by case split
--           Substitution -> "s" <> s
--         prettyFVs UnknownFVs    s = s
--         prettyFVs (KnownFVs fv) s = "fv" <> pretty (IntSet.toList fv) <> s

instance NFData e => NFData (Arg e) where
  rnf (Arg a b) = rnf a `seq` rnf b

instance LensArgInfo (Arg a) where
  getArgInfo        = argInfo
  setArgInfo ai arg = arg { argInfo = ai }
  mapArgInfo f arg  = arg { argInfo = f $ argInfo arg }

-- The other lenses are defined through LensArgInfo

instance LensHiding (Arg e) where
  getHiding = getHidingArgInfo
  setHiding = setHidingArgInfo
  mapHiding = mapHidingArgInfo

instance LensModality (Arg e) where
  getModality = getModalityArgInfo
  setModality = setModalityArgInfo
  mapModality = mapModalityArgInfo

instance LensOrigin (Arg e) where
  getOrigin = getOriginArgInfo
  setOrigin = setOriginArgInfo
  mapOrigin = mapOriginArgInfo

instance LensFreeVariables (Arg e) where
  getFreeVariables = getFreeVariablesArgInfo
  setFreeVariables = setFreeVariablesArgInfo
  mapFreeVariables = mapFreeVariablesArgInfo

-- Since we have LensModality, we get relevance and quantity by default

instance LensRelevance (Arg e) where
  getRelevance = getRelevanceMod
  setRelevance = setRelevanceMod
  mapRelevance = mapRelevanceMod

instance LensQuantity (Arg e) where
  getQuantity = getQuantityMod
  setQuantity = setQuantityMod
  mapQuantity = mapQuantityMod

instance LensCohesion (Arg e) where
  getCohesion = getCohesionMod
  setCohesion = setCohesionMod
  mapCohesion = mapCohesionMod

instance LensModalPolarity (Arg e) where
  getModalPolarity = getPolarityMod
  setModalPolarity = setPolarityMod
  mapModalPolarity = mapPolarityMod

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
-- * Named arguments
---------------------------------------------------------------------------

-- | Something potentially carrying a name.
data Named name a =
    Named { nameOf     :: Maybe name
          , namedThing :: a
          }
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- | Standard naming.
type Named_ = Named NamedName

-- | Standard argument names.
type NamedName = WithOrigin (Ranged ArgName)

-- | Equality of argument names of things modulo 'Range' and 'Origin'.
sameName :: NamedName -> NamedName -> Bool
sameName = (==) `on` (rangedThing . woThing)

unnamed :: a -> Named name a
unnamed = Named Nothing

isUnnamed :: Named name a -> Maybe a
isUnnamed = \case
  Named Nothing a -> Just a
  Named Just{}  a -> Nothing

named :: name -> a -> Named name a
named = Named . Just

userNamed :: Ranged ArgName -> a -> Named_ a
userNamed = Named . Just . WithOrigin UserWritten

-- | Accessor/editor for the 'nameOf' component.
class LensNamed a where
  -- | The type of the name
  type NameOf a
  lensNamed :: Lens' a (Maybe (NameOf a))

  -- Lenses lift through decorations:
  default lensNamed :: (Decoration f, LensNamed b, NameOf b ~ NameOf a, f b ~ a) => Lens' a (Maybe (NameOf a))
  lensNamed = traverseF . lensNamed

instance LensNamed a => LensNamed (Arg a) where
  type NameOf (Arg a) = NameOf a

instance LensNamed (Maybe a) where
  type NameOf (Maybe a) = a
  lensNamed = id

instance LensNamed (Named name a) where
  type NameOf (Named name a) = name

  lensNamed f (Named mn a) = f mn <&> \ mn' -> Named mn' a

getNameOf :: LensNamed a => a -> Maybe (NameOf a)
getNameOf a = a ^. lensNamed

setNameOf :: LensNamed a => Maybe (NameOf a) -> a -> a
setNameOf = set lensNamed

mapNameOf :: LensNamed a => (Maybe (NameOf a) -> Maybe (NameOf a)) -> a -> a
mapNameOf = over lensNamed

bareNameOf :: (LensNamed a, NameOf a ~ NamedName) => a -> Maybe ArgName
bareNameOf a = rangedThing . woThing <$> getNameOf a

bareNameWithDefault :: (LensNamed a, NameOf a ~ NamedName) => ArgName -> a -> ArgName
bareNameWithDefault x a = maybe x (rangedThing . woThing) $ getNameOf a

-- | Equality of argument names of things modulo 'Range' and 'Origin'.
namedSame :: (LensNamed a, LensNamed b, NameOf a ~ NamedName, NameOf b ~ NamedName) => a -> b -> Bool
namedSame a b = case (getNameOf a, getNameOf b) of
  (Nothing, Nothing) -> True
  (Just x , Just y ) -> sameName x y
  _ -> False

-- | Does an argument @arg@ fit the shape @dom@ of the next expected argument?
--
--   The hiding has to match, and if the argument has a name, it should match
--   the name of the domain.
--
--   'Nothing' should be '__IMPOSSIBLE__', so use as
--   @@
--     fromMaybe __IMPOSSIBLE__ $ fittingNamedArg arg dom
--   @@
--
fittingNamedArg
  :: ( LensNamed arg, NameOf arg ~ NamedName, LensHiding arg
     , LensNamed dom, NameOf dom ~ NamedName, LensHiding dom )
  => arg -> dom -> Maybe Bool
fittingNamedArg arg dom
    | not $ sameHiding arg dom = no
    | visible arg              = yes
    | otherwise =
        caseMaybe (bareNameOf arg) yes        $ \ x ->
        caseMaybe (bareNameOf dom) impossible $ \ y ->
        return $ x == y
  where
    yes = return True
    no  = return False
    impossible = Nothing

-- Standard instances for 'Named':

instance Decoration (Named name) where
  traverseF f (Named n a) = Named n <$> f a

instance HasRange a => HasRange (Named name a) where
    getRange = getRange . namedThing

instance SetRange a => SetRange (Named name a) where
  setRange r = fmap $ setRange r

instance (KillRange name, KillRange a) => KillRange (Named name a) where
  killRange (Named n a) = Named (killRange n) (killRange a)

-- instance Show a => Show (Named_ a) where
--     show (Named Nothing a)  = show a
--     show (Named (Just n) a) = rawNameToString (rangedThing n) ++ " = " ++ show a

-- -- Defined in Concrete.Pretty
-- instance Pretty a => Pretty (Named_ a) where
--     pretty (Named Nothing a)  = pretty a
--     pretty (Named (Just n) a) = text (rawNameToString (rangedThing n)) <+> "=" <+> pretty a

instance (NFData name, NFData a) => NFData (Named name a) where
  rnf (Named a b) = rnf a `seq` rnf b

-- | Only 'Hidden' arguments can have names.
type NamedArg a = Arg (Named_ a)

-- | Get the content of a 'NamedArg'.
namedArg :: NamedArg a -> a
namedArg = namedThing . unArg

defaultNamedArg :: a -> NamedArg a
defaultNamedArg = unnamedArg defaultArgInfo

unnamedArg :: ArgInfo -> a -> NamedArg a
unnamedArg info = Arg info . unnamed

-- | The functor instance for 'NamedArg' would be ambiguous,
--   so we give it another name here.
updateNamedArg :: (a -> b) -> NamedArg a -> NamedArg b
updateNamedArg = fmap . fmap

updateNamedArgA :: Applicative f => (a -> f b) -> NamedArg a -> f (NamedArg b)
updateNamedArgA = traverse . traverse

-- | @setNamedArg a b = updateNamedArg (const b) a@
setNamedArg :: NamedArg a -> b -> NamedArg b
setNamedArg a b = (b <$) <$> a

-- ** ArgName

-- | Names in binders and arguments.
type ArgName = String

argNameToString :: ArgName -> String
argNameToString = id

stringToArgName :: String -> ArgName
stringToArgName = id

appendArgNames :: ArgName -> ArgName -> ArgName
appendArgNames = (++)

---------------------------------------------------------------------------
-- * Range decoration.
---------------------------------------------------------------------------

-- | Thing with range info.
data Ranged a = Ranged
  { rangeOf     :: Range
  , rangedThing :: a
  }
  deriving (Show, Functor, Foldable, Traversable)

-- | Thing with no range info.
unranged :: a -> Ranged a
unranged = Ranged noRange

-- | Ignores range.
instance Pretty a => Pretty (Ranged a) where
  pretty = pretty . rangedThing

-- | Ignores range.
instance Eq a => Eq (Ranged a) where
  (==) = (==) `on` rangedThing

-- | Ignores range.
instance Ord a => Ord (Ranged a) where
  compare = compare `on` rangedThing

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
  = ConOSystem   -- ^ Inserted by system or expanded from an implicit pattern.
  | ConOCon      -- ^ User wrote a constructor (pattern).
  | ConORec      -- ^ User wrote a record (pattern).
  | ConORecWhere -- ^ User wrote a `record where`
  | ConOSplit    -- ^ Generated by interactive case splitting.
  deriving (Show, Eq, Ord, Enum, Bounded, Generic)

instance NFData ConOrigin

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
  deriving (Show, Eq, Ord, Enum, Bounded, Generic)

instance NFData ProjOrigin

instance KillRange ProjOrigin where
  killRange = id

---------------------------------------------------------------------------
-- * Infixity, access, abstract, etc.
---------------------------------------------------------------------------

-- | Functions can be defined in both infix and prefix style. See
--   'Agda.Syntax.Concrete.LHS'.
data IsInfix = InfixDef | PrefixDef
    deriving (Show, Eq, Ord)

-- ** private blocks, public imports

-- | Access modifier.
data Access
  = PrivateAccess KwRange Origin
      -- ^ Store the 'Origin' of the private block that lead to this qualifier.
      --   This is needed for more faithful printing of declarations.
      --   'KwRange' is the range of the @private@ keyword.
  | PublicAccess
    deriving (Show, Eq, Ord)

instance Pretty Access where
  pretty = text . \case
    PrivateAccess _ _ -> "private"
    PublicAccess      -> "public"

instance NFData Access where
  rnf _ = ()

instance HasRange Access where
  getRange _ = noRange

instance KillRange Access where
  killRange = id

privateAccessInserted :: Access
privateAccessInserted = PrivateAccess empty Inserted

-- ** abstract blocks

-- | Abstract or concrete.
data IsAbstract = AbstractDef | ConcreteDef
    deriving (Show, Eq, Ord, Generic)

-- | Semigroup computes if any of several is an 'AbstractDef'.
instance Semigroup IsAbstract where
  AbstractDef <> _ = AbstractDef
  ConcreteDef <> a = a

-- | Default is 'ConcreteDef'.
instance Monoid IsAbstract where
  mempty  = ConcreteDef
  mappend = (<>)

instance Boolean IsAbstract where
  fromBool True  = AbstractDef
  fromBool False = ConcreteDef

instance IsBool IsAbstract where
  toBool AbstractDef = True
  toBool ConcreteDef = False

instance KillRange IsAbstract where
  killRange = id

instance NFData IsAbstract

class LensIsAbstract a where
  lensIsAbstract :: Lens' a IsAbstract

instance LensIsAbstract IsAbstract where
  lensIsAbstract = id

-- | Is any element of a collection an 'AbstractDef'.
class AnyIsAbstract a where
  anyIsAbstract :: a -> IsAbstract

  default anyIsAbstract :: (Foldable t, AnyIsAbstract b, t b ~ a) => a -> IsAbstract
  anyIsAbstract = Fold.foldMap anyIsAbstract

instance AnyIsAbstract IsAbstract where
  anyIsAbstract = id

instance AnyIsAbstract a => AnyIsAbstract [a] where
instance AnyIsAbstract a => AnyIsAbstract (Maybe a) where

-- ** instance blocks

-- | Is this definition eligible for instance search?
data IsInstance
  = InstanceDef KwRange  -- ^ Range of the @instance@ keyword.
  | NotInstanceDef
    deriving (Show, Eq, Ord)

instance KillRange IsInstance where
  killRange = \case
    InstanceDef _    -> InstanceDef empty
    i@NotInstanceDef -> i

instance HasRange IsInstance where
  getRange = \case
    InstanceDef r  -> getRange r
    NotInstanceDef -> noRange

instance NFData IsInstance where
  rnf (InstanceDef _) = ()
  rnf NotInstanceDef  = ()

-- ** macro blocks

-- | Is this a macro definition?
data IsMacro = MacroDef | NotMacroDef
  deriving (Show, Eq, Ord, Generic)

instance KillRange IsMacro where killRange = id
instance HasRange  IsMacro where getRange _ = noRange

instance NFData IsMacro

-- ** opaque blocks

-- | Opaque or transparent.
data IsOpaque
  = OpaqueDef {-# UNPACK #-} !OpaqueId
    -- ^ This definition is opaque, and it is guarded by the given
    -- opaque block.
  | TransparentDef
  deriving (Show, Eq, Ord, Generic)

instance KillRange IsOpaque where
  killRange = id

instance NFData IsOpaque

class LensIsOpaque a where
  lensIsOpaque :: Lens' a IsOpaque

instance LensIsOpaque IsOpaque where
  lensIsOpaque = id

-- | Monoid representing the combined opaque blocks of a 'Foldable'
-- containing possibly-opaque declarations.
data JointOpacity
  = UniqueOpaque    {-# UNPACK #-} !OpaqueId
  -- ^ Every definition agrees on what opaque block they belong to.
  | DifferentOpaque !(HashSet OpaqueId)
  -- ^ More than one opaque block was found.
  | NoOpaque
  -- ^ Nothing here is opaque.

instance Semigroup JointOpacity where
  UniqueOpaque i <> UniqueOpaque j
    | i == j    = UniqueOpaque i
    | otherwise = DifferentOpaque (HashSet.fromList [i, j])

  DifferentOpaque is <> UniqueOpaque j     = DifferentOpaque (HashSet.insert j is)
  UniqueOpaque i     <> DifferentOpaque js = DifferentOpaque (HashSet.insert i js)
  DifferentOpaque is <> DifferentOpaque js = DifferentOpaque (HashSet.union is js)

  NoOpaque <> x = x
  x <> NoOpaque = x

instance Monoid JointOpacity where
  mappend = (<>)
  mempty = NoOpaque

class AllAreOpaque a where
  jointOpacity :: a -> JointOpacity

  default jointOpacity :: (Foldable t, AllAreOpaque b, t b ~ a) => a -> JointOpacity
  jointOpacity = Fold.foldMap jointOpacity

instance AllAreOpaque IsOpaque where
  jointOpacity = \case
    TransparentDef -> NoOpaque
    OpaqueDef i    -> UniqueOpaque i

instance AllAreOpaque a => AllAreOpaque [a] where
instance AllAreOpaque a => AllAreOpaque (Maybe a) where

---------------------------------------------------------------------------
-- * NameId
---------------------------------------------------------------------------

-- | The unique identifier of a name. Second argument is the top-level module
--   identifier.
data NameId = NameId {-# UNPACK #-} !Word64 {-# UNPACK #-} !ModuleNameHash
    deriving (Eq, Ord, Generic, Show)

instance KillRange NameId where
  killRange = id

instance Pretty NameId where
  pretty (NameId n m) = text $ show n ++ "@" ++ show m

instance Enum NameId where
  succ (NameId n m)     = NameId (n + 1) m
  pred (NameId n m)     = NameId (n - 1) m
  toEnum n              = __IMPOSSIBLE__  -- should not be used
  fromEnum (NameId n _) = fromIntegral n

instance NFData NameId where
  rnf (NameId _ _) = ()

instance Hashable NameId where
  {-# INLINE hashWithSalt #-}
  hashWithSalt salt (NameId n (ModuleNameHash m)) = hashWithSalt salt (n, m)

---------------------------------------------------------------------------
-- * Meta variables
---------------------------------------------------------------------------

-- | Meta-variable identifiers use the same structure as 'NameId's.

data MetaId = MetaId
  { metaId     :: {-# UNPACK #-} !Word64
  , metaModule :: {-# UNPACK #-} !ModuleNameHash
  }
  deriving (Eq, Ord, Generic)

instance Pretty MetaId where
  pretty (MetaId n m) =
    text $ "_" ++ show n ++ "@" ++ show (moduleNameHash m)

instance Enum MetaId where
  succ MetaId{..} = MetaId { metaId = succ metaId, .. }
  pred MetaId{..} = MetaId { metaId = pred metaId, .. }

  -- The following functions should not be used.
  toEnum   = __IMPOSSIBLE__
  fromEnum = __IMPOSSIBLE__

-- | The record selectors are not included in the resulting strings.

instance Show MetaId where
  showsPrec p (MetaId n m) = showParen (p > 0) $
    showString "MetaId " .
    showsPrec 11 n .
    showString " " .
    showsPrec 11 m

instance NFData MetaId where
  rnf (MetaId x y) = rnf x `seq` rnf y

instance Hashable MetaId where
  {-# INLINE hashWithSalt #-}
  hashWithSalt salt (MetaId n m) = hashWithSalt salt (n, m)

newtype Constr a = Constr a

-----------------------------------------------------------------------------
-- * Problems
-----------------------------------------------------------------------------

-- | A "problem" consists of a set of constraints and the same constraint can be part of multiple
--   problems.
newtype ProblemId = ProblemId Nat
  deriving (Eq, Ord, Enum, Real, Integral, Num, NFData)

-- This particular Show instance is ok because of the Num instance.
instance Show   ProblemId where show   (ProblemId n) = show n
instance Pretty ProblemId where pretty (ProblemId n) = pretty n

-- | The unique identifier of an opaque block. Second argument is the
-- top-level module identifier.
data OpaqueId = OpaqueId {-# UNPACK #-} !Word64 {-# UNPACK #-} !ModuleNameHash
    deriving (Eq, Ord, Generic, Show)

instance KillRange OpaqueId where
  killRange = id

instance Pretty OpaqueId where
  pretty (OpaqueId n m) = text $ show n ++ "@" ++ show m

instance Enum OpaqueId where
  succ (OpaqueId n m)     = OpaqueId (n + 1) m
  pred (OpaqueId n m)     = OpaqueId (n - 1) m
  toEnum n                = __IMPOSSIBLE__  -- should not be used
  fromEnum (OpaqueId n _) = fromIntegral n

instance NFData OpaqueId where
  rnf (OpaqueId _ _) = ()

instance Hashable OpaqueId where
  {-# INLINE hashWithSalt #-}
  hashWithSalt salt (OpaqueId n (ModuleNameHash m)) = hashWithSalt salt (n, m)

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
  deriving (Eq, Ord, Functor, Foldable, Traversable, Show)

-- | An abbreviation: @noPlaceholder = 'NoPlaceholder'
-- 'Strict.Nothing'@.

noPlaceholder :: e -> MaybePlaceholder e
noPlaceholder = NoPlaceholder Strict.Nothing

instance HasRange a => HasRange (MaybePlaceholder a) where
  getRange Placeholder{}       = noRange
  getRange (NoPlaceholder _ e) = getRange e

instance KillRange a => KillRange (MaybePlaceholder a) where
  killRange p@Placeholder{}     = p
  killRange (NoPlaceholder p e) = killRangeN (NoPlaceholder p) e

instance NFData a => NFData (MaybePlaceholder a) where
  rnf (Placeholder _)     = ()
  rnf (NoPlaceholder _ a) = rnf a

---------------------------------------------------------------------------
-- * Interaction meta variables
---------------------------------------------------------------------------

newtype InteractionId = InteractionId { interactionId :: Nat }
    deriving ( Eq
             , Ord
             , Show
             , Num
             , Integral
             , Real
             , Enum
             , NFData
             )

instance Pretty InteractionId where
    pretty (InteractionId i) = text $ "?" ++ show i

instance KillRange InteractionId where killRange = id

---------------------------------------------------------------------------
-- * Fixity
---------------------------------------------------------------------------

-- | Precedence levels for operators.

type PrecedenceLevel = Double

data FixityLevel
  = Unrelated
    -- ^ No fixity declared.
  | Related !PrecedenceLevel
    -- ^ Fixity level declared as the number.
  deriving (Eq, Ord, Show)

instance Null FixityLevel where
  null Unrelated = True
  null Related{} = False
  empty = Unrelated

instance NFData FixityLevel where
  rnf Unrelated   = ()
  rnf (Related _) = ()

-- | Associativity.

data Associativity = NonAssoc | LeftAssoc | RightAssoc
   deriving (Eq, Ord, Show)

-- | Fixity of operators.

data Fixity = Fixity
  { fixityRange :: Range
    -- ^ Range of the whole fixity declaration.
  , fixityLevel :: !FixityLevel
  , fixityAssoc :: !Associativity
  }
  deriving Show

noFixity :: Fixity
noFixity = Fixity noRange Unrelated NonAssoc

defaultFixity :: Fixity
defaultFixity = Fixity noRange (Related 20) NonAssoc

-- For @instance Pretty Fixity@, see Agda.Syntax.Concrete.Pretty

instance Eq Fixity where
  f1 == f2 = compare f1 f2 == EQ

instance Ord Fixity where
  compare = compare `on` (fixityLevel &&& fixityAssoc)

instance Null Fixity where
  null  = null . fixityLevel
  empty = noFixity

instance HasRange Fixity where
  getRange = fixityRange

instance KillRange Fixity where
  killRange f = f { fixityRange = noRange }

instance NFData Fixity where
  rnf (Fixity _ _ _) = ()     -- Ranges are not forced, the other fields are strict.

-- * Notation coupled with 'Fixity'

-- | The notation is handled as the fixity in the renamer.
--   Hence, they are grouped together in this type.
data Fixity' = Fixity'
    { theFixity   :: !Fixity
    , theNotation :: Notation
    , theNameRange :: Range
      -- ^ Range of the name in the fixity declaration
      --   (used for correct highlighting, see issue #2140).
    }
  deriving Show

noFixity' :: Fixity'
noFixity' = Fixity' noFixity noNotation noRange

instance Eq Fixity' where
  Fixity' f n _ == Fixity' f' n' _ = f == f' && n == n'

instance Null Fixity' where
  null (Fixity' f n _) = null f && null n
  empty = noFixity'

instance NFData Fixity' where
  rnf (Fixity' _ a _) = rnf a

instance KillRange Fixity' where
  killRange (Fixity' f n r) = killRangeN Fixity' f n r

-- lenses

_fixityAssoc :: Lens' Fixity Associativity
_fixityAssoc f r = f (fixityAssoc r) <&> \x -> r { fixityAssoc = x }

_fixityLevel :: Lens' Fixity FixityLevel
_fixityLevel f r = f (fixityLevel r) <&> \x -> r { fixityLevel = x }

-- Lens focusing on Fixity

class LensFixity a where
  lensFixity :: Lens' a Fixity

instance LensFixity Fixity where
  lensFixity = id

instance LensFixity Fixity' where
  lensFixity f fix' = f (theFixity fix') <&> \ fx -> fix' { theFixity = fx }

-- Lens focusing on Fixity'

class LensFixity' a where
  lensFixity' :: Lens' a Fixity'

instance LensFixity' Fixity' where
  lensFixity' = id

---------------------------------------------------------------------------
-- * Import directive
---------------------------------------------------------------------------

-- | The things you are allowed to say when you shuffle names between name
--   spaces (i.e. in @import@, @namespace@, or @open@ declarations).
data ImportDirective' n m = ImportDirective
  { importDirRange :: Range
  , using          :: Using' n m
  , hiding         :: HidingDirective' n m
  , impRenaming    :: RenamingDirective' n m
  , publicOpen     :: Maybe KwRange
      -- ^ Only for @open@. Exports the opened names from the current module.
      --   Range of the @public@ keyword.
  }
  deriving Eq

type HidingDirective'   n m = [ImportedName' n m]
type RenamingDirective' n m = [Renaming' n m]

-- | @null@ for import directives holds when everything is imported unchanged
--   (no names are hidden or renamed).
instance Null (ImportDirective' n m) where
  null = \case
    ImportDirective _ UseEverything [] [] _ -> True
    _ -> False
  empty = defaultImportDir

instance (HasRange n, HasRange m) => Semigroup (ImportDirective' n m) where
  i1 <> i2 = ImportDirective
    { importDirRange = fuseRange i1 i2
    , using          = using i1 <> using i2
    , hiding         = hiding i1 ++ hiding i2
    , impRenaming    = impRenaming i1 ++ impRenaming i2
    , publicOpen     = publicOpen i1 <|> publicOpen i2
    }

instance (HasRange n, HasRange m) => Monoid (ImportDirective' n m) where
  mempty  = empty
  mappend = (<>)

-- | Default is directive is @private@ (use everything, but do not export).
defaultImportDir :: ImportDirective' n m
defaultImportDir = ImportDirective noRange UseEverything [] [] Nothing

-- | @isDefaultImportDir@ implies @null@, but not the other way round.
isDefaultImportDir :: ImportDirective' n m -> Bool
isDefaultImportDir dir = null dir && null (publicOpen dir)

-- | The @using@ clause of import directive.
data Using' n m
  = UseEverything              -- ^ No @using@ clause given.
  | Using [ImportedName' n m]  -- ^ @using@ the specified names.
  deriving Eq

instance Semigroup (Using' n m) where
  UseEverything <> u             = u
  u             <> UseEverything = u
  Using xs      <> Using ys      = Using (xs ++ ys)

instance Monoid (Using' n m) where
  mempty  = UseEverything
  mappend = (<>)

instance Null (Using' n m) where
  null UseEverything = True
  null Using{}       = False
  empty = mempty

mapUsing :: ([ImportedName' n1 m1] -> [ImportedName' n2 m2]) -> Using' n1 m1 -> Using' n2 m2
mapUsing f = \case
  UseEverything -> UseEverything
  Using xs      -> Using $ f xs

-- | An imported name can be a module or a defined name.
data ImportedName' n m
  = ImportedModule  m  -- ^ Imported module name of type @m@.
  | ImportedName    n  -- ^ Imported name of type @n@.
  deriving (Eq, Ord, Show)

fromImportedName :: ImportedName' a a -> a
fromImportedName = \case
  ImportedModule x -> x
  ImportedName   x -> x

setImportedName :: ImportedName' a a -> a -> ImportedName' a a
setImportedName (ImportedName   x) y = ImportedName   y
setImportedName (ImportedModule x) y = ImportedModule y

-- | Like 'partitionEithers'.
partitionImportedNames :: [ImportedName' n m] -> ([n], [m])
partitionImportedNames = flip foldr ([], []) $ \case
  ImportedName   n -> first  (n:)
  ImportedModule m -> second (m:)

-- -- Defined in Concrete.Pretty
-- instance (Pretty n, Pretty m) => Pretty (ImportedName' n m) where
--   pretty (ImportedModule x) = "module" <+> pretty x
--   pretty (ImportedName   x) = pretty x

-- instance (Show n, Show m) => Show (ImportedName' n m) where
--   show (ImportedModule x) = "module " ++ show x
--   show (ImportedName   x) = show x

data Renaming' n m = Renaming
  { renFrom    :: ImportedName' n m
    -- ^ Rename from this name.
  , renTo      :: ImportedName' n m
    -- ^ To this one.  Must be same kind as 'renFrom'.
  , renFixity  :: Maybe Fixity
    -- ^ New fixity of 'renTo' (optional).
  , renToRange :: Range
    -- ^ The range of the \"to\" keyword.  Retained for highlighting purposes.
  }
  deriving Eq

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
    killRangeN (\u h r -> ImportDirective noRange u h r (p $> empty)) u h r

instance (KillRange a, KillRange b) => KillRange (Using' a b) where
  killRange (Using  i) = killRangeN Using  i
  killRange UseEverything = UseEverything

instance (KillRange a, KillRange b) => KillRange (Renaming' a b) where
  killRange (Renaming i n mf _to) = killRangeN (\ i n mf -> Renaming i n mf noRange) i n mf

instance (KillRange a, KillRange b) => KillRange (ImportedName' a b) where
  killRange (ImportedModule n) = killRangeN ImportedModule n
  killRange (ImportedName   n) = killRangeN ImportedName   n

-- ** NFData instances

-- | Ranges are not forced.

instance (NFData a, NFData b) => NFData (ImportDirective' a b) where
  rnf (ImportDirective _ a b c _) = rnf a `seq` rnf b `seq` rnf c

instance (NFData a, NFData b) => NFData (Using' a b) where
  rnf UseEverything = ()
  rnf (Using a)     = rnf a

-- | Ranges are not forced.

instance (NFData a, NFData b) => NFData (Renaming' a b) where
  rnf (Renaming a b c _) = rnf a `seq` rnf b `seq` rnf c

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
    deriving (Show, Eq, Functor)

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
data PositivityCheck = YesPositivityCheck | NoPositivityCheck
  deriving (Eq, Ord, Show, Bounded, Enum, Generic)

instance KillRange PositivityCheck where
  killRange = id

-- Semigroup and Monoid via conjunction
instance Semigroup PositivityCheck where
  NoPositivityCheck <> _ = NoPositivityCheck
  _ <> NoPositivityCheck = NoPositivityCheck
  _ <> _ = YesPositivityCheck

instance Monoid PositivityCheck where
  mempty  = YesPositivityCheck
  mappend = (<>)

instance NFData PositivityCheck

-----------------------------------------------------------------------------
-- * Universe checking
-----------------------------------------------------------------------------

-- | Universe check? (Default is yes).
data UniverseCheck = YesUniverseCheck | NoUniverseCheck
  deriving (Eq, Ord, Show, Bounded, Enum, Generic)

instance KillRange UniverseCheck where
  killRange = id

instance NFData UniverseCheck

-----------------------------------------------------------------------------
-- * Universe checking
-----------------------------------------------------------------------------

-- | Coverage check? (Default is yes).
data CoverageCheck = YesCoverageCheck | NoCoverageCheck
  deriving (Eq, Ord, Show, Bounded, Enum, Generic)

instance KillRange CoverageCheck where
  killRange = id

-- Semigroup and Monoid via conjunction
instance Semigroup CoverageCheck where
  NoCoverageCheck <> _ = NoCoverageCheck
  _ <> NoCoverageCheck = NoCoverageCheck
  _ <> _ = YesCoverageCheck

instance Monoid CoverageCheck where
  mempty  = YesCoverageCheck
  mappend = (<>)

instance NFData CoverageCheck

-----------------------------------------------------------------------------
-- * Rewrite Directives on the LHS
-----------------------------------------------------------------------------

-- | @RewriteEqn' qn p e@ represents the @rewrite@ and irrefutable @with@
--   clauses of the LHS.
--   @qn@ stands for the QName of the auxiliary function generated to implement the feature
--   @nm@ is the type of names for pattern variables
--   @p@  is the type of patterns
--   @e@  is the type of expressions

data RewriteEqn' qn nm p e
  = Rewrite (List1 (qn, e))             -- ^ @rewrite e@
  | Invert qn (List1 (Named nm (p, e))) -- ^ @with p <- e in eq@
  | LeftLet (List1 (p, e))              -- ^ @using p <- e@
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance (NFData qn, NFData nm, NFData p, NFData e) => NFData (RewriteEqn' qn nm p e) where
  rnf = \case
    Rewrite es    -> rnf es
    Invert qn pes -> rnf (qn, pes)
    LeftLet pes   -> rnf pes

instance (Pretty nm, Pretty p, Pretty e) => Pretty (RewriteEqn' qn nm p e) where
  pretty = \case
    Rewrite es   -> prefixedThings (text "rewrite") $ List1.toList (pretty . snd <$> es)
    LeftLet pes  -> prefixedThings (text "using") [pretty p <+> "<-" <+> pretty e | (p, e) <- List1.toList pes]
    Invert _ pes -> prefixedThings (text "invert") $ List1.toList (namedWith <$> pes) where

      namedWith (Named nm (p, e)) =
        let patexp = pretty p <+> "<-" <+> pretty e in
        case nm of
          Nothing -> patexp
          Just nm -> pretty nm <+> ":" <+> patexp

instance (HasRange qn, HasRange nm, HasRange p, HasRange e) => HasRange (RewriteEqn' qn nm p e) where
  getRange = \case
    Rewrite es    -> getRange es
    Invert qn pes -> getRange (qn, pes)
    LeftLet pes   -> getRange pes

instance (KillRange qn, KillRange nm, KillRange e, KillRange p) => KillRange (RewriteEqn' qn nm p e) where
  killRange = \case
    Rewrite es    -> killRangeN Rewrite es
    Invert qn pes -> killRangeN Invert qn pes
    LeftLet pes   -> killRangeN LeftLet pes

-----------------------------------------------------------------------------
-- * Information on expanded ellipsis (@...@)
-----------------------------------------------------------------------------

-- ^ When the ellipsis in a clause is expanded, we remember that we
--   did so. We also store the number of with-arguments that are
--   included in the expanded ellipsis.
data ExpandedEllipsis
  = ExpandedEllipsis
  { ellipsisRange :: Range
  , ellipsisWithArgs :: Int
  }
  | NoEllipsis
  deriving (Show, Eq)

instance Null ExpandedEllipsis where
  null  = (== NoEllipsis)
  empty = NoEllipsis

instance Semigroup ExpandedEllipsis where
  NoEllipsis <> e          = e
  e          <> NoEllipsis = e
  (ExpandedEllipsis r1 k1) <> (ExpandedEllipsis r2 k2) = ExpandedEllipsis (r1 <> r2) (k1 + k2)

instance Monoid ExpandedEllipsis where
  mempty  = NoEllipsis
  mappend = (<>)

instance KillRange ExpandedEllipsis where
  killRange (ExpandedEllipsis _ k) = ExpandedEllipsis noRange k
  killRange NoEllipsis             = NoEllipsis

instance NFData ExpandedEllipsis where
  rnf (ExpandedEllipsis _ a) = rnf a
  rnf NoEllipsis             = ()

-- | Notation as provided by the @syntax@ declaration.
type Notation = [NotationPart]

noNotation :: Notation
noNotation = []

-- | Positions of variables in syntax declarations.

data BoundVariablePosition = BoundVariablePosition
  { holeNumber :: !Int
    -- ^ The position (in the left-hand side of the syntax
    -- declaration) of the hole in which the variable is bound,
    -- counting from zero (and excluding parts that are not holes).
    -- For instance, for @syntax Σ A (λ x → B) = B , A , x@ the number
    -- for @x@ is @1@, corresponding to @B@ (@0@ would correspond to
    -- @A@).
  , varNumber :: !Int
    -- ^ The position in the list of variables for this particular
    -- variable, counting from zero, and including wildcards. For
    -- instance, for @syntax F (λ x _ y → A) = y ! A ! x@ the number
    -- for @x@ is @0@, the number for @_@ is @1@, and the number for
    -- @y@ is @2@.
  }
  deriving (Eq, Ord, Show)

-- | Notation parts.

data NotationPart
  = IdPart RString
    -- ^ An identifier part. For instance, for @_+_@ the only
    -- identifier part is @+@.
  | HolePart Range (NamedArg (Ranged Int))
    -- ^ A hole: a place where argument expressions can be written.
    -- For instance, for @_+_@ the two underscores are holes, and for
    -- @syntax Σ A (λ x → B) = B , A , x@ the variables @A@ and @B@
    -- are holes. The number is the position of the hole, counting
    -- from zero. For instance, the number for @A@ is @0@, and the
    -- number for @B@ is @1@.
  | VarPart Range (Ranged BoundVariablePosition)
    -- ^ A bound variable.
    --
    -- The first range is the range of the variable in the right-hand
    -- side of the syntax declaration, and the second range is the
    -- range of the variable in the left-hand side.
  | WildPart (Ranged BoundVariablePosition)
    -- ^ A wildcard (an underscore in binding position).
  deriving Show

instance Eq NotationPart where
  VarPart _ i  == VarPart _ j  = i == j
  HolePart _ x == HolePart _ y = x == y
  WildPart i   == WildPart j   = i == j
  IdPart x     == IdPart y     = x == y
  _            == _            = False

instance Ord NotationPart where
  VarPart _ i  `compare` VarPart _ j  = i `compare` j
  HolePart _ x `compare` HolePart _ y = x `compare` y
  WildPart i   `compare` WildPart j   = i `compare` j
  IdPart x     `compare` IdPart y     = x `compare` y
  VarPart{}    `compare` _            = LT
  _            `compare` VarPart{}    = GT
  HolePart{}   `compare` _            = LT
  _            `compare` HolePart{}   = GT
  WildPart{}   `compare` _            = LT
  _            `compare` WildPart{}   = GT

instance HasRange NotationPart where
  getRange = \case
    IdPart x     -> getRange x
    VarPart r _  -> r
    WildPart i   -> getRange i
    HolePart r _ -> r

instance SetRange NotationPart where
  setRange r = \case
    IdPart x     -> IdPart x
    VarPart _ i  -> VarPart r i
    WildPart i   -> WildPart i
    HolePart _ i -> HolePart r i

instance KillRange NotationPart where
  killRange = \case
    IdPart x     -> IdPart $ killRange x
    VarPart _ i  -> VarPart noRange $ killRange i
    WildPart i   -> WildPart $ killRange i
    HolePart _ x -> HolePart noRange $ killRange x

instance NFData BoundVariablePosition where
  rnf = (`seq` ())

instance NFData NotationPart where
  rnf (VarPart _ a)  = rnf a
  rnf (HolePart _ a) = rnf a
  rnf (WildPart a)   = rnf a
  rnf (IdPart a)     = rnf a
