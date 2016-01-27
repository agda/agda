{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell    #-}

-- | Occurrences.

module Agda.TypeChecking.Positivity.Occurrence
  ( Occurrence(..)
  , boundToEverySome
  , productOfEdgesInBoundedWalk
  , Agda.TypeChecking.Positivity.Occurrence.tests
  ) where

import Control.Applicative
import Control.DeepSeq
import Control.Monad
import Data.Either
import Data.Maybe
import Data.Typeable (Typeable)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Test.QuickCheck

import Agda.Syntax.Position
import Agda.Utils.Graph.AdjacencyMap.Unidirectional (Graph)
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as Graph
import Agda.Utils.List
import Agda.Utils.Null
import Agda.Utils.SemiRing

#include "undefined.h"
import Agda.Utils.Impossible

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

-- | The map contains bindings of the form @bound |-> es@, satisfying
-- the following property: for every non-empty list @w@,
-- @'foldr1' 'otimes' w '<=' bound@ iff
-- @'or' [ 'all' every w '&&' 'any' some w | (every, some) <- ess ]@.

boundToEverySome ::
  Map Occurrence [(Occurrence -> Bool, Occurrence -> Bool)]
boundToEverySome = Map.fromList
  [ ( JustPos
    , [((/= Unused), (`elem` [Mixed, JustNeg, JustPos]))]
    )
  , ( StrictPos
    , [ ((/= Unused), (`elem` [Mixed, JustNeg, JustPos]))
      , ((not . (`elem` [Unused, GuardPos])), const True)
      ]
    )
  , ( GuardPos
    , [((/= Unused), const True)]
    )
  ]

-- | @productOfEdgesInBoundedWalk occ g u v bound@ returns @'Just' e@
-- iff there is a walk @c@ (a list of edges) in @g@, from @u@ to @v@,
-- for which the product @'foldr1' 'otimes' ('map' occ c) '<=' bound@.
-- In this case the returned value @e@ is the product @'foldr1'
-- 'otimes' c@ for one such walk.
--
-- Preconditions: @u@ and @v@ must belong to @g@, and @bound@ must
-- belong to the domain of @boundToEverySome@.

-- There is a property for this function in
-- Agda.Utils.Graph.AdjacencyMap.Unidirectional.Tests.

productOfEdgesInBoundedWalk ::
  (SemiRing e, Ord n) =>
  (e -> Occurrence) -> Graph n n e -> n -> n -> Occurrence -> Maybe e
productOfEdgesInBoundedWalk occ g u v bound =
  case Map.lookup bound boundToEverySome of
    Nothing  -> __IMPOSSIBLE__
    Just ess ->
      case msum [ Graph.walkSatisfying (every . occ) (some . occ) g u v
                | (every, some) <- ess
                ] of
        Just es@(_ : _) -> Just (foldr1 otimes (map Graph.label es))
        Just []         -> __IMPOSSIBLE__
        Nothing         -> Nothing

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

-- | Is the given predicate satisfiable?

satisfiable :: (Occurrence -> Bool) -> Bool
satisfiable p = or [ p o | o <- [minBound .. maxBound] ]

-- Some properties that are used in the implementation of
-- prop_boundToEverySome2.

prop_boundToEverySome0 :: Bool
prop_boundToEverySome0 = and
  [ length ess >= 1
      &&
    all satisfiable ps
      &&
    and [ p minBound | p <- ps ]
      &&
    all (\p -> satisfiable (not . p)) [ e | (e, _) <- ess ]
      &&
    and [ not (p maxBound) | p <- ps, satisfiable (not . p) ]
  | (_, ess) <- Map.toList boundToEverySome
  , let ps = concat [ [e, s] | (e, s) <- ess ]
  ]

-- A simple property that does not always generate enough interesting
-- test cases.

prop_boundToEverySome1 :: NonEmptyList Occurrence -> Property
prop_boundToEverySome1 (NonEmpty w) =
  forAll (elements $ Map.toList boundToEverySome) $ \(bound, ess) ->
    (foldr1 otimes w <= bound)
      ==
    or [ all every w && any some w | (every, some) <- ess ]

-- A more complicated property that does not always generate enough
-- interesting test cases.

prop_boundToEverySome2 :: Property
prop_boundToEverySome2 =
  forAll (elements $ Map.toList boundToEverySome) $ \(bound, ess) ->
    (forAll (oneof [ do os1 <- listOf (arbitrary `suchThat` every)
                        o   <- arbitrary
                                 `suchThat` (\o -> every o && some o)
                        os2 <- listOf (arbitrary `suchThat` every)
                        return (os1 ++ [o] ++ os2)
                   | (every, some) <- ess
                   ]) $ \w ->
       foldr1 otimes w <= bound)
      .&&.
    (forAll (do
         ess <- mapM (\(e, s) ->
                         elements
                           (Left e :
                            [ Right s | satisfiable (not . s) ])) ess
         let (es, ss) = partitionEithers ess
             every    = \o -> and [ not (s o) | s <- ss ]
             some e   = \o -> every o && not (e o)
             everyG   = arbitrary `suchThat` every
             segment  = listOf everyG
         os <- uniqOn id <$> mapM (\e -> arbitrary `suchThat` some e) es
         if Prelude.null os
           then listOf1 everyG
           else (++) <$> listOf everyG
                     <*> (concat <$>
                            mapM (\o -> (o :) <$> listOf everyG) os))
       (\w -> not (foldr1 otimes w <= bound)))

------------------------------------------------------------------------

-- Template Haskell hack to make the following $quickCheckAll work
-- under GHC 7.8.
return []

-- | Tests.

tests :: IO Bool
tests = do
  putStrLn "Agda.TypeChecking.Positivity.Occurrence"
  $quickCheckAll
