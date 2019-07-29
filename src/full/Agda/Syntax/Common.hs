{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-} -- for type equality ~
{-# LANGUAGE UndecidableInstances       #-} -- for functional dependency: LensNamed name (Arg a)

{-| Some common syntactic entities are defined in this module.
-}
module Agda.Syntax.Common where

import Prelude hiding (null)

import Control.DeepSeq

#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup hiding (Arg)
#endif
import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as ByteString
import Data.Foldable ()
import Data.Function
import Data.Hashable (Hashable(..))
import qualified Data.Strict.Maybe as Strict
import Data.Data (Data)
import Data.Word
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import GHC.Generics (Generic)

import Agda.Syntax.Position

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.Maybe
import Agda.Utils.Null
import Agda.Utils.PartialOrd
import Agda.Utils.POMonoid
import Agda.Utils.Pretty

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Delayed
---------------------------------------------------------------------------

-- | Used to specify whether something should be delayed.
data Delayed = Delayed | NotDelayed
  deriving (Data, Show, Eq, Ord)

instance KillRange Delayed where
  killRange = id

---------------------------------------------------------------------------
-- * File
---------------------------------------------------------------------------

data FileType = AgdaFileType | MdFileType | RstFileType | TexFileType | OrgFileType
  deriving (Data, Eq, Ord, Show)

instance Pretty FileType where
  pretty = \case
    AgdaFileType -> "Agda"
    MdFileType   -> "Markdown"
    RstFileType  -> "ReStructedText"
    TexFileType  -> "LaTeX"
    OrgFileType  -> "org-mode"

---------------------------------------------------------------------------
-- * Eta-equality
---------------------------------------------------------------------------

data HasEta = NoEta | YesEta
  deriving (Data, Show, Eq, Ord)

instance HasRange HasEta where
  getRange _ = noRange

instance KillRange HasEta where
  killRange = id

instance NFData HasEta where
  rnf NoEta  = ()
  rnf YesEta = ()

---------------------------------------------------------------------------
-- * Induction
---------------------------------------------------------------------------

data Induction = Inductive | CoInductive
  deriving (Data, Eq, Ord, Show)

instance Pretty Induction where
  pretty Inductive   = "inductive"
  pretty CoInductive = "coinductive"

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

data Overlappable = YesOverlap | NoOverlap
  deriving (Data, Show, Eq, Ord)

data Hiding  = Hidden | Instance Overlappable | NotHidden
  deriving (Data, Show, Eq, Ord)

instance Pretty Hiding where
  pretty = \case
    Hidden     -> "hidden"
    NotHidden  -> "visible"
    Instance{} -> "instance"

-- | Just for the 'Hiding' instance. Should never combine different
--   overlapping.
instance Semigroup Overlappable where
  NoOverlap  <> NoOverlap  = NoOverlap
  YesOverlap <> YesOverlap = YesOverlap
  _          <> _          = __IMPOSSIBLE__

-- | 'Hiding' is an idempotent partial monoid, with unit 'NotHidden'.
--   'Instance' and 'NotHidden' are incompatible.
instance Semigroup Hiding where
  NotHidden  <> h           = h
  h          <> NotHidden   = h
  Hidden     <> Hidden      = Hidden
  Instance o <> Instance o' = Instance (o <> o')
  _          <> _           = __IMPOSSIBLE__

instance Monoid Overlappable where
  mempty  = NoOverlap
  mappend = (<>)

instance Monoid Hiding where
  mempty = NotHidden
  mappend = (<>)

instance KillRange Hiding where
  killRange = id

instance NFData Overlappable where
  rnf NoOverlap  = ()
  rnf YesOverlap = ()

instance NFData Hiding where
  rnf Hidden       = ()
  rnf (Instance o) = rnf o
  rnf NotHidden    = ()

-- | Decorating something with 'Hiding' information.
data WithHiding a = WithHiding
  { whHiding :: !Hiding
  , whThing  :: a
  }
  deriving (Data, Eq, Ord, Show, Functor, Foldable, Traversable)

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

isOverlappable :: LensHiding a => a -> Bool
isOverlappable x =
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

-- | We have a tuple of modalities, which might not be fully orthogonal.
--   For instance, irrelevant stuff is also run-time irrelevant.
data Modality = Modality
  { modRelevance :: Relevance
      -- ^ Legacy irrelevance.
      --   See Pfenning, LiCS 2001; Abel/Vezzosi/Winterhalter, ICFP 2017.
  , modQuantity  :: Quantity
      -- ^ Cardinality / runtime erasure.
      --   See Conor McBride, I got plenty o' nutting, Wadlerfest 2016.
      --   See Bob Atkey, Syntax and Semantics of Quantitative Type Theory, LiCS 2018.
  , modCohesion :: Cohesion
      -- ^ Cohesion/what was in Agda-flat.
      --   see "Brouwer's fixed-point theorem in real-cohesive homotopy type theory" (arXiv:1509.07584)
      --   Currently only the comonad is implemented.
  } deriving (Data, Eq, Ord, Show, Generic)

defaultModality :: Modality
defaultModality = Modality defaultRelevance defaultQuantity defaultCohesion

-- | Pointwise composition.
instance Semigroup Modality where
  Modality r q c <> Modality r' q' c' = Modality (r <> r') (q <> q') (c <> c')

-- | Pointwise unit.
instance Monoid Modality where
  mempty = Modality mempty mempty mempty
  mappend = (<>)

-- | Dominance ordering.
instance PartialOrd Modality where
  comparable (Modality r q c) (Modality r' q' c') = comparable (r, (q, c)) (r', (q', c'))

instance POSemigroup Modality where
instance POMonoid Modality where

instance LeftClosedPOMonoid Modality where
  inverseCompose = inverseComposeModality

-- | @m `moreUsableModality` m'@ means that an @m@ can be used
--   where ever an @m'@ is required.

moreUsableModality :: Modality -> Modality -> Bool
moreUsableModality m m' = related m POLE m'

usableModality :: LensModality a => a -> Bool
usableModality a = usableRelevance m && usableQuantity m
  where m = getModality a

-- | Multiplicative monoid (standard monoid).
composeModality :: Modality -> Modality -> Modality
composeModality = (<>)

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
inverseComposeModality (Modality r q c) (Modality r' q' c') =
  Modality (r `inverseComposeRelevance` r')
           (q `inverseComposeQuantity`  q')
           (c `inverseComposeCohesion`  c')

-- | Left division by a 'Modality'.
--   Used e.g. to modify context when going into a @m@ argument.
inverseApplyModality :: LensModality a => Modality -> a -> a
inverseApplyModality m = mapModality (m `inverseComposeModality`)

-- | 'Modality' forms a pointwise additive monoid.
addModality :: Modality -> Modality -> Modality
addModality (Modality r q c) (Modality r' q' c') = Modality (addRelevance r r') (addQuantity q q') (addCohesion c c')

zeroModality :: Modality
zeroModality = Modality zeroRelevance zeroQuantity zeroCohesion

-- | Absorptive element under addition.
topModality :: Modality
topModality = Modality topRelevance topQuantity topCohesion

-- | Equality ignoring origin.

sameModality :: Modality -> Modality -> Bool
sameModality (Modality r q c) (Modality r' q' c') = sameRelevance r r' && sameQuantity q q' && sameCohesion c c'

-- boilerplate instances

instance KillRange Modality where
  killRange = id

instance NFData Modality where

-- Lens stuff

lModRelevance :: Lens' Relevance Modality
lModRelevance f m = f (modRelevance m) <&> \ r -> m { modRelevance = r }

lModQuantity :: Lens' Quantity Modality
lModQuantity f m = f (modQuantity m) <&> \ q -> m { modQuantity = q }

lModCohesion :: Lens' Cohesion Modality
lModCohesion f m = f (modCohesion m) <&> \ q -> m { modCohesion = q }

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

-- default accessors for Relevance

getRelevanceMod :: LensModality a => LensGet Relevance a
getRelevanceMod = getRelevance . getModality

setRelevanceMod :: LensModality a => LensSet Relevance a
setRelevanceMod = mapModality . setRelevance

mapRelevanceMod :: LensModality a => LensMap Relevance a
mapRelevanceMod = mapModality . mapRelevance

-- default accessors for Quantity

getQuantityMod :: LensModality a => LensGet Quantity a
getQuantityMod = getQuantity . getModality

setQuantityMod :: LensModality a => LensSet Quantity a
setQuantityMod = mapModality . setQuantity

mapQuantityMod :: LensModality a => LensMap Quantity a
mapQuantityMod = mapModality . mapQuantity

-- default accessors for Cohesion

getCohesionMod :: LensModality a => LensGet Cohesion a
getCohesionMod = getCohesion . getModality

setCohesionMod :: LensModality a => LensSet Cohesion a
setCohesionMod = mapModality . setCohesion

mapCohesionMod :: LensModality a => LensMap Cohesion a
mapCohesionMod = mapModality . mapCohesion

---------------------------------------------------------------------------
-- * Quantities
---------------------------------------------------------------------------

-- ** Quantity origin.

-- | Origin of 'Quantity0'.
data Q0Origin
  = Q0Inferred       -- ^ User wrote nothing.
  | Q0       Range   -- ^ User wrote "@0".
  | Q0Erased Range   -- ^ User wrote "@erased".
  deriving (Data, Show, Generic, Eq, Ord)

-- | Origin of 'Quantity1'.
data Q1Origin
  = Q1Inferred       -- ^ User wrote nothing.
  | Q1       Range   -- ^ User wrote "@1".
  | Q1Linear Range   -- ^ User wrote "@linear".
  deriving (Data, Show, Generic, Eq, Ord)

-- | Origin of 'Quantityω'.
data QωOrigin
  = QωInferred       -- ^ User wrote nothing.
  | Qω       Range   -- ^ User wrote "@ω".
  | QωPlenty Range   -- ^ User wrote "@plenty".
  deriving (Data, Show, Generic, Eq, Ord)

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
  deriving (Data, Show, Generic, Eq, Ord)
    -- @Ord@ instance in case @Quantity@ is used in keys for maps etc.

defaultQuantity :: Quantity
defaultQuantity = topQuantity

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
instance Semigroup Quantity where
  Quantity1{} <> q = q           -- right-bias!
  q <> Quantity1{} = q
  _ <> Quantity0 o = Quantity0 o -- right-bias!
  Quantity0 o <> _ = Quantity0 o
  _omega <> qomega = qomega      -- right-bias!

-- | In the absense of finite quantities besides 0, ω is the unit.
--   Otherwise, 1 is the unit.
instance Monoid Quantity where
  mempty  = Quantity1 mempty
  mappend = (<>)

-- | Note that the order is @ω ≤ 0,1@, more options is smaller.
instance PartialOrd Quantity where
  comparable = curry $ \case
    (q, q') | sameQuantity q q' -> POEQ
    -- ω is least
    (Quantityω{}, _)  -> POLT
    (_, Quantityω{})  -> POGT
    -- others are uncomparable
    _ -> POAny

instance POSemigroup Quantity where
instance POMonoid Quantity where

instance LeftClosedPOMonoid Quantity where
  inverseCompose = inverseComposeQuantity

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

zeroQuantity :: Quantity
zeroQuantity = Quantity0 mempty

-- | Absorptive element is ω.
topQuantity :: Quantity
topQuantity = Quantityω mempty

-- | @m `moreUsableQuantity` m'@ means that an @m@ can be used
--   where ever an @m'@ is required.

moreQuantity :: Quantity -> Quantity -> Bool
moreQuantity m m' = related m POLE m'

composeQuantity :: Quantity -> Quantity -> Quantity
composeQuantity = (<>)

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

---------------------------------------------------------------------------
-- * Relevance
---------------------------------------------------------------------------

-- | A function argument can be relevant or irrelevant.
--   See "Agda.TypeChecking.Irrelevance".
data Relevance
  = Relevant    -- ^ The argument is (possibly) relevant at compile-time.
  | NonStrict   -- ^ The argument may never flow into evaluation position.
                --   Therefore, it is irrelevant at run-time.
                --   It is treated relevantly during equality checking.
  | Irrelevant  -- ^ The argument is irrelevant at compile- and runtime.
    deriving (Data, Show, Eq, Enum, Bounded, Generic)

allRelevances :: [Relevance]
allRelevances = [minBound..maxBound]

defaultRelevance :: Relevance
defaultRelevance = Relevant

instance HasRange Relevance where
  getRange _ = noRange

instance SetRange Relevance where
  setRange _ = id

instance KillRange Relevance where
  killRange rel = rel -- no range to kill

instance NFData Relevance where
  rnf Relevant   = ()
  rnf NonStrict  = ()
  rnf Irrelevant = ()

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

isRelevant :: LensRelevance a => a -> Bool
isRelevant a = getRelevance a == Relevant

isIrrelevant :: LensRelevance a => a -> Bool
isIrrelevant a = getRelevance a == Irrelevant

isNonStrict :: LensRelevance a => a -> Bool
isNonStrict a = getRelevance a == NonStrict

-- | Information ordering.
-- @Relevant  \`moreRelevant\`
--  NonStrict \`moreRelevant\`
--  Irrelevant@
moreRelevant :: Relevance -> Relevance -> Bool
moreRelevant = (<=)

-- | Equality ignoring origin.
sameRelevance :: Relevance -> Relevance -> Bool
sameRelevance = (==)

-- | More relevant is smaller.
instance Ord Relevance where
  compare = curry $ \case
    (r, r') | r == r' -> EQ
    -- top
    (_, Irrelevant) -> LT
    (Irrelevant, _) -> GT
    -- bottom
    (Relevant, _) -> LT
    (_, Relevant) -> GT
    -- redundant case
    (NonStrict,NonStrict) -> EQ

-- | More relevant is smaller.
instance PartialOrd Relevance where
  comparable = comparableOrd

-- | @usableRelevance rel == False@ iff we cannot use a variable of @rel@.
usableRelevance :: LensRelevance a => a -> Bool
usableRelevance a = case getRelevance a of
  Irrelevant -> False
  NonStrict  -> False
  Relevant   -> True

-- | 'Relevance' composition.
--   'Irrelevant' is dominant, 'Relevant' is neutral.
--   Composition coincides with 'max'.
composeRelevance :: Relevance -> Relevance -> Relevance
composeRelevance r r' =
  case (r, r') of
    (Irrelevant, _) -> Irrelevant
    (_, Irrelevant) -> Irrelevant
    (NonStrict, _)  -> NonStrict
    (_, NonStrict)  -> NonStrict
    (Relevant, Relevant) -> Relevant

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
inverseComposeRelevance r x =
  case (r, x) of
    (Relevant  , x)          -> x          -- going to relevant arg.: nothing changes
                                           -- because Relevant is comp.-neutral
    (Irrelevant, x)          -> Relevant   -- going irrelevant: every thing usable
    (NonStrict , Irrelevant) -> Irrelevant -- otherwise: irrelevant things remain unusable
    (NonStrict , _)          -> Relevant   -- but @NonStrict@s become usable

-- | Left division by a 'Relevance'.
--   Used e.g. to modify context when going into a @rel@ argument.
inverseApplyRelevance :: LensRelevance a => Relevance -> a -> a
inverseApplyRelevance rel = mapRelevance (rel `inverseComposeRelevance`)

-- | 'Relevance' forms a semigroup under composition.
instance Semigroup Relevance where
  (<>) = composeRelevance

-- | 'Relevant' is the unit.
instance Monoid Relevance where
  mempty  = Relevant
  mappend = (<>)

instance POSemigroup Relevance where
instance POMonoid Relevance where

instance LeftClosedPOMonoid Relevance where
  inverseCompose = inverseComposeRelevance

-- | Combine inferred 'Relevance'.
--   The unit is 'Irrelevant'.
addRelevance :: Relevance -> Relevance -> Relevance
addRelevance = min

-- | 'Relevance' forms a monoid under addition, and even a semiring.
zeroRelevance :: Relevance
zeroRelevance = Irrelevant

-- | Absorptive element under addition.
topRelevance :: Relevance
topRelevance = Relevant

-- | Irrelevant function arguments may appear non-strictly in the codomain type.
irrToNonStrict :: Relevance -> Relevance
irrToNonStrict Irrelevant = NonStrict
irrToNonStrict rel        = rel

-- | Applied when working on types (unless --experimental-irrelevance).
nonStrictToRel :: Relevance -> Relevance
nonStrictToRel NonStrict = Relevant
nonStrictToRel rel       = rel

nonStrictToIrr :: Relevance -> Relevance
nonStrictToIrr NonStrict = Irrelevant
nonStrictToIrr rel       = rel

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
    deriving (Data, Show, Eq, Enum, Bounded, Generic)

allCohesions :: [Cohesion]
allCohesions = [minBound..maxBound]

defaultCohesion :: Cohesion
defaultCohesion = Continuous

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
    (Squash, x)       -> Squash     -- artificial case, should not be needed.
    (Flat , Flat)     -> Flat       -- otherwise: Flat things remain Flat
    (Flat , _)        -> Squash     -- but everything else becomes unusable.

-- | Left division by a 'Cohesion'.
--   Used e.g. to modify context when going into a @rel@ argument.
inverseApplyCohesion :: LensCohesion a => Cohesion -> a -> a
inverseApplyCohesion rel = mapCohesion (rel `inverseComposeCohesion`)

-- | 'Cohesion' forms a semigroup under composition.
instance Semigroup Cohesion where
  (<>) = composeCohesion

-- | 'Continous' is the unit.
instance Monoid Cohesion where
  mempty  = Continuous
  mappend = (<>)

instance POSemigroup Cohesion where
instance POMonoid Cohesion where

instance LeftClosedPOMonoid Cohesion where
  inverseCompose = inverseComposeCohesion

-- | Combine inferred 'Cohesion'.
--   The unit is 'Squash'.
addCohesion :: Cohesion -> Cohesion -> Cohesion
addCohesion = min

-- | 'Cohesion' forms a monoid under addition, and even a semiring.
zeroCohesion :: Cohesion
zeroCohesion = Squash

-- | Absorptive element under addition.
topCohesion :: Cohesion
topCohesion = Flat

---------------------------------------------------------------------------
-- * Origin of arguments (user-written, inserted or reflected)
---------------------------------------------------------------------------

-- | Origin of arguments.
data Origin
  = UserWritten  -- ^ From the source file / user input.  (Preserve!)
  | Inserted     -- ^ E.g. inserted hidden arguments.
  | Reflected    -- ^ Produced by the reflection machinery.
  | CaseSplit    -- ^ Produced by an interactive case split.
  | Substitution -- ^ Named application produced to represent a substitution. E.g. "?0 (x = n)" instead of "?0 n"
  deriving (Data, Show, Eq, Ord)

instance KillRange Origin where
  killRange = id

instance NFData Origin where
  rnf UserWritten = ()
  rnf Inserted = ()
  rnf Reflected = ()
  rnf CaseSplit = ()
  rnf Substitution = ()

-- | Decorating something with 'Origin' information.
data WithOrigin a = WithOrigin
  { woOrigin :: !Origin
  , woThing  :: a
  }
  deriving (Data, Eq, Ord, Show, Functor, Foldable, Traversable)

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
  deriving (Data, Eq, Ord, Show)

instance Semigroup FreeVariables where
  UnknownFVs   <> _            = UnknownFVs
  _            <> UnknownFVs   = UnknownFVs
  KnownFVs vs1 <> KnownFVs vs2 = KnownFVs (IntSet.union vs1 vs2)

instance Monoid FreeVariables where
  mempty  = KnownFVs IntSet.empty
  mappend = (<>)

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
  } deriving (Data, Eq, Ord, Show)

instance KillRange ArgInfo where
  killRange i = i -- There are no ranges in ArgInfo's

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

defaultArgInfo :: ArgInfo
defaultArgInfo =  ArgInfo
  { argInfoHiding        = NotHidden
  , argInfoModality      = defaultModality
  , argInfoOrigin        = UserWritten
  , argInfoFreeVariables = UnknownFVs
  }

-- Accessing through ArgInfo

-- default accessors for Hiding

getHidingArgInfo :: LensArgInfo a => LensGet Hiding a
getHidingArgInfo = getHiding . getArgInfo

setHidingArgInfo :: LensArgInfo a => LensSet Hiding a
setHidingArgInfo = mapArgInfo . setHiding

mapHidingArgInfo :: LensArgInfo a => LensMap Hiding a
mapHidingArgInfo = mapArgInfo . mapHiding

-- default accessors for Modality

getModalityArgInfo :: LensArgInfo a => LensGet Modality a
getModalityArgInfo = getModality . getArgInfo

setModalityArgInfo :: LensArgInfo a => LensSet Modality a
setModalityArgInfo = mapArgInfo . setModality

mapModalityArgInfo :: LensArgInfo a => LensMap Modality a
mapModalityArgInfo = mapArgInfo . mapModality

-- default accessors for Origin

getOriginArgInfo :: LensArgInfo a => LensGet Origin a
getOriginArgInfo = getOrigin . getArgInfo

setOriginArgInfo :: LensArgInfo a => LensSet Origin a
setOriginArgInfo = mapArgInfo . setOrigin

mapOriginArgInfo :: LensArgInfo a => LensMap Origin a
mapOriginArgInfo = mapArgInfo . mapOrigin

-- default accessors for FreeVariables

getFreeVariablesArgInfo :: LensArgInfo a => LensGet FreeVariables a
getFreeVariablesArgInfo = getFreeVariables . getArgInfo

setFreeVariablesArgInfo :: LensArgInfo a => LensSet FreeVariables a
setFreeVariablesArgInfo = mapArgInfo . setFreeVariables

mapFreeVariablesArgInfo :: LensArgInfo a => LensMap FreeVariables a
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
  } deriving (Data, Eq, Ord, Show, Functor, Foldable, Traversable)

instance Decoration Arg where
  traverseF f (Arg ai a) = Arg ai <$> f a

instance HasRange a => HasRange (Arg a) where
    getRange = getRange . unArg

instance SetRange a => SetRange (Arg a) where
  setRange r = fmap $ setRange r

instance KillRange a => KillRange (Arg a) where
  killRange (Arg info a) = killRange2 Arg info a

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
--           Irrelevant   -> "." ++ s
--           NonStrict    -> "?" ++ s
--           Relevant     -> "r" ++ s -- Andreas: I want to see it explicitly
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
--           NonStrict    -> "?" <> s
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
    deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)

-- | Standard naming.
type Named_ = Named NamedName

-- | Standard argument names.
type NamedName = WithOrigin (Ranged ArgName)

-- | Equality of argument names of things modulo 'Range' and 'Origin'.
sameName :: NamedName -> NamedName -> Bool
sameName = (==) `on` (rangedThing . woThing)

unnamed :: a -> Named name a
unnamed = Named Nothing

named :: name -> a -> Named name a
named = Named . Just

userNamed :: Ranged ArgName -> a -> Named_ a
userNamed = Named . Just . WithOrigin UserWritten

-- | Accessor/editor for the 'nameOf' component.
class LensNamed name a | a -> name where
  lensNamed :: Lens' (Maybe name) a

  -- Lenses lift through decorations:
  default lensNamed :: (Decoration f, LensNamed name b, f b ~ a) => Lens' (Maybe name) a
  lensNamed = traverseF . lensNamed

instance LensNamed name a => LensNamed name (Arg a) where

instance LensNamed name (Maybe name) where
  lensNamed = id

instance LensNamed name (Named name a) where
  lensNamed f (Named mn a) = f mn <&> \ mn' -> Named mn' a

getNameOf :: LensNamed name a => a -> Maybe name
getNameOf a = a ^. lensNamed

setNameOf :: LensNamed name a => Maybe name -> a -> a
setNameOf = set lensNamed

mapNameOf :: LensNamed name a => (Maybe name -> Maybe name) -> a -> a
mapNameOf = over lensNamed

bareNameOf :: LensNamed NamedName a => a -> Maybe ArgName
bareNameOf a = rangedThing . woThing <$> getNameOf a

bareNameWithDefault :: LensNamed NamedName a => ArgName -> a -> ArgName
bareNameWithDefault x a = maybe x (rangedThing . woThing) $ getNameOf a

-- | Equality of argument names of things modulo 'Range' and 'Origin'.
namedSame :: (LensNamed NamedName a, LensNamed NamedName b) => a -> b -> Bool
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
  :: ( LensNamed NamedName arg, LensHiding arg
     , LensNamed NamedName dom, LensHiding dom )
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
  deriving (Data, Show, Functor, Foldable, Traversable)

-- | Thing with no range info.
unranged :: a -> Ranged a
unranged = Ranged noRange

instance Pretty a => Pretty (Ranged a) where
  pretty = pretty . rangedThing

-- instance Show a => Show (Ranged a) where
--   show = show . rangedThing

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
  | ConOSplit   -- ^ Generated by interactive case splitting.
  deriving (Data, Show, Eq, Ord, Enum, Bounded)

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
  deriving (Data, Show, Eq, Ord, Enum, Bounded)

instance KillRange ProjOrigin where
  killRange = id

data DataOrRecord = IsData | IsRecord
  deriving (Data, Eq, Ord, Show)

---------------------------------------------------------------------------
-- * Infixity, access, abstract, etc.
---------------------------------------------------------------------------

-- | Functions can be defined in both infix and prefix style. See
--   'Agda.Syntax.Concrete.LHS'.
data IsInfix = InfixDef | PrefixDef
    deriving (Data, Show, Eq, Ord)

-- | Access modifier.
data Access
  = PrivateAccess Origin
      -- ^ Store the 'Origin' of the private block that lead to this qualifier.
      --   This is needed for more faithful printing of declarations.
  | PublicAccess
  | OnlyQualified  -- ^ Visible from outside, but not exported when opening the module
                             --   Used for qualified constructors.
    deriving (Data, Show, Eq, Ord)

instance Pretty Access where
  pretty = text . \case
    PrivateAccess _ -> "private"
    PublicAccess    -> "public"
    OnlyQualified   -> "only-qualified"

instance NFData Access where
  rnf _ = ()

instance HasRange Access where
  getRange _ = noRange

instance KillRange Access where
  killRange = id

-- | Abstract or concrete
data IsAbstract = AbstractDef | ConcreteDef
    deriving (Data, Show, Eq, Ord)

instance KillRange IsAbstract where
  killRange = id

-- | Is this definition eligible for instance search?
data IsInstance = InstanceDef | NotInstanceDef
    deriving (Data, Show, Eq, Ord)

instance KillRange IsInstance where
  killRange = id

instance HasRange IsInstance where
  getRange _ = noRange

instance NFData IsInstance where
  rnf InstanceDef    = ()
  rnf NotInstanceDef = ()

-- | Is this a macro definition?
data IsMacro = MacroDef | NotMacroDef
  deriving (Data, Show, Eq, Ord)

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
    deriving (Eq, Ord, Data, Generic, Show)

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
  hashWithSalt salt (NameId n m) = hashWithSalt salt (n, m)

---------------------------------------------------------------------------
-- * Meta variables
---------------------------------------------------------------------------

-- | A meta variable identifier is just a natural number.
--
newtype MetaId = MetaId { metaId :: Nat }
    deriving (Eq, Ord, Num, Real, Enum, Integral, Data, Generic)

instance Pretty MetaId where
  pretty (MetaId n) = text $ "_" ++ show n

-- | Show non-record version of this newtype.
instance Show MetaId where
  showsPrec p (MetaId n) = showParen (p > 0) $
    showString "MetaId " . shows n

instance NFData MetaId where
  rnf (MetaId x) = rnf x

instance Hashable MetaId

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
  deriving (Show, Eq, Ord, Data)

-- | Placeholders are used to represent the underscores in a section.

data MaybePlaceholder e
  = Placeholder !PositionInName
  | NoPlaceholder !(Strict.Maybe PositionInName) e
    -- ^ The second argument is used only (but not always) for name
    -- parts other than underscores.
  deriving (Data, Eq, Ord, Functor, Foldable, Traversable, Show)

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
    deriving ( Eq
             , Ord
             , Show
             , Num
             , Integral
             , Real
             , Enum
             , Data
             )

instance Pretty InteractionId where
    pretty (InteractionId i) = text $ "?" ++ show i

instance KillRange InteractionId where killRange = id

-----------------------------------------------------------------------------
-- * Import directive
-----------------------------------------------------------------------------

-- | The things you are allowed to say when you shuffle names between name
--   spaces (i.e. in @import@, @namespace@, or @open@ declarations).
data ImportDirective' n m = ImportDirective
  { importDirRange :: Range
  , using          :: Using' n m
  , hiding         :: [ImportedName' n m]
  , impRenaming    :: [Renaming' n m]
  , publicOpen     :: Bool -- ^ Only for @open@. Exports the opened names from the current module.
  }
  deriving (Data, Eq)

data Using' n m = UseEverything | Using [ImportedName' n m]
  deriving (Data, Eq)

instance Semigroup (Using' n m) where
  UseEverything <> u             = u
  u             <> UseEverything = u
  Using xs      <> Using ys      = Using (xs ++ ys)

instance Monoid (Using' n m) where
  mempty  = UseEverything
  mappend = (<>)

-- | Default is directive is @private@ (use everything, but do not export).
defaultImportDir :: ImportDirective' n m
defaultImportDir = ImportDirective noRange UseEverything [] [] False

isDefaultImportDir :: ImportDirective' n m -> Bool
isDefaultImportDir (ImportDirective _ UseEverything [] [] False) = True
isDefaultImportDir _                                             = False

-- | An imported name can be a module or a defined name.
data ImportedName' n m
  = ImportedModule  m  -- ^ Imported module name of type @m@.
  | ImportedName    n  -- ^ Imported name of type @n@.
  deriving (Data, Eq, Ord, Show)

setImportedName :: ImportedName' a a -> a -> ImportedName' a a
setImportedName (ImportedName   x) y = ImportedName   y
setImportedName (ImportedModule x) y = ImportedModule y

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
  , renToRange :: Range
    -- ^ The range of the \"to\" keyword.  Retained for highlighting purposes.
  }
  deriving (Data, Eq)

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
    deriving (Data, Show, Eq, Functor)

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

-----------------------------------------------------------------------------
-- * Universe checking
-----------------------------------------------------------------------------

-- | Universe check? (Default is yes).
data UniverseCheck = YesUniverseCheck | NoUniverseCheck
  deriving (Eq, Ord, Show, Bounded, Enum, Data)

instance KillRange UniverseCheck where
  killRange = id

-----------------------------------------------------------------------------
-- * Rewrite Directives on the LHS
-----------------------------------------------------------------------------

data RewriteEqn' p e
  = Rewrite [e]      -- ^ @rewrite e@
  | Invert  [(p, e)] -- ^ @with p <- e@
  deriving (Data, Eq, Show, Functor, Foldable, Traversable)

instance (NFData p, NFData e) => NFData (RewriteEqn' p e) where
  rnf = \case
    Rewrite es -> rnf es
    Invert pes -> rnf pes

instance (Pretty p, Pretty e) => Pretty (RewriteEqn' p e) where
  pretty = \case
    Rewrite es -> prefixedThings (text "rewrite") (pretty <$> es)
    Invert pes -> prefixedThings (text "invert") (pes <&> \ (p, e) -> pretty p <+> "<-" <+> pretty e)

instance (HasRange p, HasRange e) => HasRange (RewriteEqn' p e) where
  getRange = \case
    Rewrite es -> getRange es
    Invert pes -> getRange pes

instance (KillRange e, KillRange p) => KillRange (RewriteEqn' p e) where
  killRange = \case
    Rewrite es -> killRange1 Rewrite es
    Invert pes -> killRange1 Invert pes
