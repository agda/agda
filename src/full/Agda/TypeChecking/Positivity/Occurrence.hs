{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell    #-}

-- | Occurrences.

module Agda.TypeChecking.Positivity.Occurrence where

import Control.DeepSeq
import Data.Maybe
import Data.Typeable (Typeable)
import Test.QuickCheck

import Agda.Syntax.Position
import Agda.Utils.Null
import Agda.Utils.SemiRing

-- | Subterm occurrences for positivity checking.
--   The constructors are listed in increasing information they provide:
--   @Mixed <= JustPos <= StrictPos <= GuardPos <= Unused@
--   @Mixed <= JustNeg <= Unused@.
data Occurrence
  = Mixed     -- ^ Arbitrary occurrence (positive and negative).
  | JustNeg   -- ^ Negative occurrence.
  | JustPos   -- ^ Positive occurrence, but not strictly positive.
  | StrictPos -- ^ Strictly positive occurrence.
  | GuardPos  -- ^ Guarded strictly positive occurrence (i.e., under ∞).  For checking recursive records.
  | Unused    --  ^ No occurrence.
  deriving (Typeable, Show, Eq, Ord, Enum, Bounded)

instance NFData Occurrence where rnf x = seq x ()

instance KillRange Occurrence where
  killRange = id

instance Arbitrary Occurrence where
  arbitrary = elements [minBound .. maxBound]

  shrink Unused = []
  shrink _      = [Unused]

instance CoArbitrary Occurrence where
  coarbitrary = coarbitrary . fromEnum

-- | 'Occurrence' is a complete lattice with least element 'Mixed'
--   and greatest element 'Unused'.
--
--   It forms a commutative semiring where 'oplus' is meet (glb)
--   and 'otimes' is composition. Both operations are idempotent.
--
--   For 'oplus', 'Unused' is neutral (zero) and 'Mixed' is dominant.
--   For 'otimes', 'StrictPos' is neutral (one) and 'Unused' is dominant.

instance SemiRing Occurrence where
  ozero = Unused
  oone  = StrictPos

  oplus Mixed _           = Mixed     -- dominant
  oplus _ Mixed           = Mixed
  oplus Unused o          = o         -- neutral
  oplus o Unused          = o
  oplus JustNeg  JustNeg  = JustNeg
  oplus JustNeg  o        = Mixed     -- negative and any form of positve
  oplus o        JustNeg  = Mixed
  oplus GuardPos o        = o         -- second-rank neutral
  oplus o GuardPos        = o
  oplus StrictPos o       = o         -- third-rank neutral
  oplus o StrictPos       = o
  oplus JustPos JustPos   = JustPos

  -- If the definition of otimes is changed, then
  -- Agda.TypeChecking.Positivity.checkStrictlyPositive may have to be
  -- updated. See the properties below.

  otimes Unused _            = Unused     -- dominant
  otimes _ Unused            = Unused
  otimes Mixed _             = Mixed      -- second-rank dominance
  otimes _ Mixed             = Mixed
  otimes JustNeg JustNeg     = JustPos
  otimes JustNeg _           = JustNeg    -- third-rank dominance
  otimes _ JustNeg           = JustNeg
  otimes JustPos _           = JustPos    -- fourth-rank dominance
  otimes _ JustPos           = JustPos
  otimes GuardPos _          = GuardPos   -- _ `elem` [StrictPos, GuardPos]
  otimes _ GuardPos          = GuardPos
  otimes StrictPos StrictPos = StrictPos  -- neutral

instance StarSemiRing Occurrence where
  ostar Mixed     = Mixed
  ostar JustNeg   = Mixed
  ostar JustPos   = JustPos
  ostar StrictPos = StrictPos
  ostar GuardPos  = StrictPos
  ostar Unused    = StrictPos

instance Null Occurrence where
  empty = Unused

------------------------------------------------------------------------
-- Tests

prop_Occurrence_oplus_associative ::
  Occurrence -> Occurrence -> Occurrence -> Bool
prop_Occurrence_oplus_associative x y z =
  oplus x (oplus y z) == oplus (oplus x y) z

prop_Occurrence_oplus_ozero :: Occurrence -> Bool
prop_Occurrence_oplus_ozero x =
  oplus ozero x == x

prop_Occurrence_oplus_commutative :: Occurrence -> Occurrence -> Bool
prop_Occurrence_oplus_commutative x y =
  oplus x y == oplus y x

prop_Occurrence_otimes_associative ::
  Occurrence -> Occurrence -> Occurrence -> Bool
prop_Occurrence_otimes_associative x y z =
  otimes x (otimes y z) == otimes (otimes x y) z

prop_Occurrence_otimes_oone :: Occurrence -> Bool
prop_Occurrence_otimes_oone x =
  otimes oone x == x
    &&
  otimes x oone == x

prop_Occurrence_distributive ::
  Occurrence -> Occurrence -> Occurrence -> Bool
prop_Occurrence_distributive x y z =
  otimes x (oplus y z) == oplus (otimes x y) (otimes x z)
    &&
  otimes (oplus x y) z == oplus (otimes x z) (otimes y z)

prop_Occurrence_otimes_ozero :: Occurrence -> Bool
prop_Occurrence_otimes_ozero x =
  otimes ozero x == ozero
    &&
  otimes x ozero == ozero

prop_Occurrence_ostar :: Occurrence -> Bool
prop_Occurrence_ostar x =
  ostar x == oplus oone (otimes x (ostar x))
    &&
  ostar x == oplus oone (otimes (ostar x) x)

------------------------------------------------------------------------
-- The implementation of
-- Agda.TypeChecking.Positivity.checkStrictlyPositive is based on the
-- assumption that the properties in this section hold

-- | A helper function used to construct properties.

otimesPropertyHelper
  :: (Occurrence -> Bool)        -- ^ Must not be constant.
  -> Maybe (Occurrence -> Bool)  -- ^ 'Nothing' represents
                                 -- @'const' 'True'@. If a function is
                                 -- given, then it must not be constant.
  -> Occurrence
  -> Property
otimesPropertyHelper every some' bound =
  (forAll (listOf (arbitrary `suchThat` every)) $ \os1 ->
   forAll (listOf (arbitrary `suchThat` every)) $ \os2 ->
   forAll (arbitrary `suchThat` (\o -> every o && some o)) $ \o ->
     let os = os1 ++ [o] ++ os2 in
     foldr1 otimes os <= bound)
    .&&.
  (forAll (listOf (arbitrary `suchThat` every)) $ \os1 ->
   forAll (listOf (arbitrary `suchThat` every)) $ \os2 ->
   forAll (arbitrary `suchThat` (not . every)) $ \o ->
     let os = os1 ++ [o] ++ os2 in
     not (foldr1 otimes os <= bound))
    .&&.
  (forAll arbitrary $ \os1 ->
   forAll arbitrary $ \os2 ->
   forAll (arbitrary `suchThat` (not . every)) $ \o ->
     let os = os1 ++ [o] ++ os2 in
     not (foldr1 otimes os <= bound))
    .&&.
  case some' of
    Nothing   -> property True
    Just some ->
      forAll (listOf1 (arbitrary `suchThat` (not . some))) $ \os ->
        not (foldr1 otimes os <= bound)
  where
  some = fromMaybe (const True) some'

-- ∀ nonempty list os.
-- ⨂ os ≤ JustPos
--   iff
-- no element in os is Unused, and some element in os is Mixed,
-- JustNeg, or JustPos.

prop_lessThanOrEqualToJustPos :: Property
prop_lessThanOrEqualToJustPos =
  otimesPropertyHelper
    (/= Unused) (Just (`elem` [Mixed, JustNeg, JustPos])) JustPos

-- ∀ nonempty list os.
-- ⨂ os ≤ GuardPos
--   iff
-- no element in os is Unused.

prop_lessThanOrEqualToGuardPos :: Property
prop_lessThanOrEqualToGuardPos =
  otimesPropertyHelper (/= Unused) Nothing GuardPos

-- ∀ nonempty list os.
-- ⨂ os ≤ StrictPos
--   iff
-- (no element in os is Unused, and some element in os is Mixed,
--  JustNeg, or JustPos,
--    or
--  no element in os is Unused or GuardPos).

prop_lessThanOrEqualToStrictPos :: Property
prop_lessThanOrEqualToStrictPos =
  (forAll (listOf (arbitrary `suchThat` every1)) $ \os1 ->
   forAll (listOf (arbitrary `suchThat` every1)) $ \os2 ->
   forAll (arbitrary `suchThat` (\o -> every1 o && some1 o)) $ \o ->
     let os = os1 ++ [o] ++ os2 in
     foldr1 otimes os <= bound)
    .&&.
  (forAll (listOf1 (arbitrary `suchThat` every2)) $ \os ->
     foldr1 otimes os <= bound)
    .&&.
  (forAll (listOf (arbitrary `suchThat` every2)) $ \os1 ->
   forAll (listOf (arbitrary `suchThat` every2)) $ \os2 ->
   forAll (arbitrary `suchThat` (not . every1)) $ \o ->
     let os = os1 ++ [o] ++ os2 in
     not (foldr1 otimes os <= bound))
    .&&.
  (forAll arbitrary $ \os1 ->
   forAll arbitrary $ \os2 ->
   forAll (arbitrary `suchThat` (not . every1)) $ \o ->
     let os = os1 ++ [o] ++ os2 in
     not (foldr1 otimes os <= bound))
    .&&.
  (forAll (listOf (arbitrary `suchThat` (not . some1))) $ \os1 ->
   forAll (listOf (arbitrary `suchThat` (not . some1))) $ \os2 ->
   forAll (arbitrary `suchThat` (\o ->
             not (some1 o) && not (every2 o))) $ \o ->
     let os = os1 ++ [o] ++ os2 in
     not (foldr1 otimes os <= bound))
  where
  -- Note that every2 o implies every1 o.
  every1 = (/= Unused)
  every2 = (not . (`elem` [Unused, GuardPos]))
  some1  = (`elem` [Mixed, JustNeg, JustPos])
  bound  = StrictPos

------------------------------------------------------------------------

-- Template Haskell hack to make the following $quickCheckAll work
-- under GHC 7.8.
return []

-- | Tests.

tests :: IO Bool
tests = do
  putStrLn "Agda.TypeChecking.Positivity.Occurrence"
  $quickCheckAll
