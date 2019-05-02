-- -- UNUSED


-- -- | Lexicographic order search, more or less as defined in
-- --      \"A Predicative Analysis of Structural Recursion\" by
-- --      Andreas Abel and Thorsten Altenkirch.

-- module Agda.Termination.Lexicographic
--   ( LexOrder
--   , RecBehaviour(..)
--   , Column
--   , recBehaviourInvariant
--   , fromDiagonals
--   , lexOrder
--   , Agda.Termination.Lexicographic.tests
--   ) where

-- import Data.List
-- import Data.Map (Map, (!))
-- import qualified Data.Map as Map
-- import Data.Array (Array, Ix)
-- import qualified Data.Array as Array
-- import Data.Set (Set)
-- import qualified Data.Set as Set

-- import Agda.Termination.CallGraph
-- import Agda.Termination.Matrix (Size (..))
-- import qualified Agda.Termination.Matrix as M
-- import Agda.Termination.Order

-- import Agda.Utils.Either
-- import Agda.Utils.List
-- import Agda.Utils.QuickCheck
-- import Agda.Utils.TestHelpers
-- import Agda.Utils.Tuple

-- -- | A lexicographic ordering for the recursion behaviour of a
-- -- given function is a permutation of the argument indices which can
-- -- be used to show that the function terminates. See the paper
-- -- referred to above for more details.

-- type LexOrder arg = [arg]

-- -- | A recursion behaviour expresses how a certain function calls
-- -- itself (transitively). For every argument position there is a value
-- -- ('Column') describing how the function calls itself for that
-- -- particular argument. See also 'recBehaviourInvariant'.

-- data RecBehaviour arg call =
--   RB { columns :: Map arg (Column call)
--      , calls   :: Set call
--        -- ^ The indices to the columns.
--      , size    :: Size Integer
--      }
--   deriving Show

-- -- | A column expresses how the size of a certain argument changes in
-- -- the various recursive calls a function makes to itself
-- -- (transitively).

-- type Column call = Map call Order

-- -- | 'RecBehaviour' invariant: the size must match the real size of
-- -- the recursion behaviour, and all columns must have the same
-- -- indices.

-- recBehaviourInvariant :: Eq call => RecBehaviour arg call -> Bool
-- recBehaviourInvariant rb =
--   genericLength (Map.elems $ columns rb) == cols (size rb)
--   &&
--   all (== rows (size rb))
--       (map (genericLength . Map.elems) $ Map.elems $ columns rb)
--   &&
--   allEqual (calls rb : (map Map.keysSet $ Map.elems $ columns rb))

-- -- Generates a recursion behaviour.

-- instance (Arbitrary call, Arbitrary arg, Ord arg, Ord call)
--   => Arbitrary (RecBehaviour call arg) where
--   arbitrary = do
--     calls <- fmap nub $ listOf arbitrary
--     args  <- fmap nub $ listOf arbitrary
--     let rows = genericLength calls
--         cols = genericLength args
--         sz   = Size { rows = rows, cols = cols }
--         colGen = do
--           col <- vectorOf (fromIntegral rows) arbitrary
--           return $ Map.fromList (zip calls col)
--     cols <- fmap (zip args) $ vectorOf (fromIntegral cols) colGen
--     return $ RB { columns = Map.fromList cols
--                 , calls   = Set.fromList calls
--                 , size    = sz }

-- instance (CoArbitrary call, CoArbitrary arg) => CoArbitrary (RecBehaviour call arg) where
--   coarbitrary (RB c cs s) =
--     coarbitrary (map (mapSnd Map.toList) $ Map.toList c) .
--     coarbitrary (Set.toList cs) .
--     coarbitrary s

-- prop_recBehaviour_Arbitrary :: RecBehaviour Integer Integer -> Bool
-- prop_recBehaviour_Arbitrary = recBehaviourInvariant

-- -- | Checks whether there are any calls left in the recursion
-- -- behaviour.

-- noCallsLeft :: RecBehaviour arg call -> Bool
-- noCallsLeft rb = rows (size rb) == 0

-- -- | Constructs a recursion behaviour from a list of matrix diagonals
-- -- (\"rows\"). Note that the @call@ indices do not need to be
-- -- distinct, since they are paired up with unique 'Integer's.
-- --
-- -- Precondition: all arrays should have the same bounds.

-- fromDiagonals :: (Ord call, Ix arg)
--               => [(call, Array arg Order)] -> RecBehaviour arg (Integer, call)
-- fromDiagonals []   = RB { columns = Map.fromList []
--                         , calls   = Set.empty
--                         , size    = Size 0 0 }
-- fromDiagonals rows = RB { columns = Map.fromList $ zip args cols
--                         , calls   = Set.fromList calls
--                         , size    = Size { rows = genericLength rows
--                                          , cols = genericLength cols }
--                         }
--   where
--   calls = zip [1 ..] $ map fst rows
--   cols = map Map.fromList $ map (zip calls) $ transpose $
--          map (Array.elems . snd) rows
--   args = Array.range $ Array.bounds $ snd $ head rows

-- prop_fromDiagonals m =
--   forAll (vectorOf (fromIntegral $ rows $ M.size m) arbitrary) $ \calls ->
--     let oss = zip calls $
--               map (Array.listArray (1, cols $ M.size m)) $
--               M.toLists m
--         rb = fromDiagonals oss :: RecBehaviour Integer (Integer, Bool)
--     in
--     recBehaviourInvariant rb
--     &&
--     if rows (M.size m) == 0 then
--       rows (size rb) == 0
--      else
--       size rb == M.size m

-- -- | Checks if this \"column\" is well-behaved (all calls decreasing,
-- -- at least one strictly decreasing).

-- okColumn :: Column call -> Bool
-- okColumn col = any decreasing col' && all (/= unknown) col'
--   where col' = Map.elems col

-- -- | @'newBehaviour' n rb@ computes a new recursion behaviour from
-- -- @rb@ by removing all \"rows\" (calls) for which the @n@-th element
-- -- is 'decreasing', and also completely removing the @n@-th column.
-- --
-- -- Precondition: there has to be an @n@-th column.

-- newBehaviour :: (Ord arg, Ord call)
--              => arg -> RecBehaviour arg call -> RecBehaviour arg call
-- newBehaviour n rb =
--   RB { columns = Map.map remove $ Map.delete n $ columns rb
--      , calls   = Set.difference (calls rb)
--                                 (Set.fromList indicesToRemove)
--      , size    = Size { rows = rows (size rb) -
--                                genericLength indicesToRemove
--                       , cols = cols (size rb) - 1 }
--      }
--   where
--   Just colN       = Map.lookup n $ columns rb
--   indicesToRemove = map fst $ filter (decreasing . snd) $ Map.toList colN
--   remove colJ     = foldr Map.delete colJ indicesToRemove

-- prop_newBehaviour :: RecBehaviour Integer Integer -> Property
-- prop_newBehaviour rb =
--   not (cols (size rb) == 0) ==>
--     forAll (elements $ Map.keys $ columns rb) $ \n ->
--       recBehaviourInvariant (newBehaviour n rb)

-- -- | @'correctLexOrder' rs ps@ checks that the permutation @ps@ really
-- -- induces a lexicographic ordering which shows that the function
-- -- represented by the recursion behaviour @rs@ terminates.

-- correctLexOrder :: (Ord arg, Ord call)
--                 => RecBehaviour arg call -> LexOrder arg -> Bool
-- correctLexOrder rb []        = noCallsLeft rb
-- correctLexOrder rb (p0 : ps) =
--   okColumn (columns rb ! p0) && correctLexOrder (newBehaviour p0 rb) ps

-- -- | Tries to compute a lexicographic ordering for the given recursion
-- -- behaviour. This algorithm should be complete.
-- --
-- -- If no lexicographic ordering can be found, then two sets are
-- -- returned:
-- --
-- -- * A set of argument positions which are not properly decreasing, and
-- --
-- -- * the calls where these problems show up.

-- lexOrder :: (Ord arg, Ord call) =>
--   RecBehaviour arg call -> Either (Set arg, Set call) (LexOrder arg)
-- lexOrder rb | noCallsLeft rb = Right []
--             | otherwise      = case okColumns of
--   []      -> Left (Map.keysSet $ columns rb, calls rb)
--   (n : _) -> case lexOrder (newBehaviour n rb) of
--     Left err -> Left err
--     Right ps -> Right $ n : ps
--   where
--   okColumns = map fst $ filter snd $
--               map (mapSnd okColumn) $
--               Map.toList $ columns rb

-- prop_lexOrder :: RecBehaviour Integer Integer -> Property
-- prop_lexOrder rb =
--   let mPerm = lexOrder rb
--       Right perm = mPerm
--   in
--   isRight mPerm ==>
--     classify (cols (size rb) >= 2) "interesting" $
--     correctLexOrder rb perm

-- prop_lexOrder_noArgs =
--   forAll positive $ \n ->
--     isLeft (lexOrder $ rb n)
--     where rb :: Integer -> RecBehaviour Integer Integer
--           rb n = RB { columns = Map.empty
--                     , calls   = Set.fromList [1 .. n]
--                     , size    = Size { rows = n, cols = 0 }
--                     }

-- ------------------------------------------------------------------------
-- -- All tests

-- tests :: IO Bool
-- tests = runTests "Agda.Termination.Lexicographic"
--   [ quickCheck' prop_recBehaviour_Arbitrary
--   , quickCheck' prop_fromDiagonals
--   , quickCheck' prop_newBehaviour
--   , quickCheckWith' stdArgs{ maxSuccess = 50
--                            , maxDiscardRatio = 4
--                            , maxSize    = 20
--                            }
--                     prop_lexOrder
--   , quickCheck' prop_lexOrder_noArgs
--   ]
