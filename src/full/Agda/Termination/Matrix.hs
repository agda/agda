{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | Naive implementation of simple matrix library.

-- Originally copied from Agda1 sources.

module Agda.Termination.Matrix
  ( -- * Basic data types
    Matrix
  , matrixInvariant
  , Size(..)
  , sizeInvariant
  , MIx (..)
  , mIxInvariant
    -- * Generating and creating matrices
  , fromLists
  , fromIndexList
  , toLists
  , Agda.Termination.Matrix.zipWith
  , matrix
  , matrixUsingRowGen
    -- * Combining and querying matrices
  , size
  , square
  , isEmpty
  , add
  , mul
  , diagonal
    -- * Modifying matrices
  , addRow
  , addColumn
    -- * Tests
  , Agda.Termination.Matrix.tests
  ) where

import Data.Array
import Data.List as List
import Agda.Utils.QuickCheck
import Agda.Utils.TestHelpers
import Agda.Termination.Semiring (Semiring,SemiRing)
import qualified Agda.Termination.Semiring as Semiring

------------------------------------------------------------------------
-- Basic data types

-- | This matrix type is used for tests.

type TM = Matrix Integer Integer

-- | Size of a matrix.

data Size i = Size { rows :: i, cols :: i }
  deriving (Eq, Show)

sizeInvariant :: (Ord i, Num i) => Size i -> Bool
sizeInvariant sz = rows sz >= 0 && cols sz >= 0

instance (Arbitrary i, Integral i) => Arbitrary (Size i) where
  arbitrary = do
    r <- natural
    c <- natural
    return $ Size { rows = fromInteger r, cols = fromInteger c }

instance CoArbitrary i => CoArbitrary (Size i) where
  coarbitrary (Size rs cs) = coarbitrary rs . coarbitrary cs

prop_Arbitrary_Size :: Size Integer -> Bool
prop_Arbitrary_Size = sizeInvariant

-- | Converts a size to a set of bounds suitable for use with
-- the matrices in this module.

toBounds :: Num i => Size i -> (MIx i, MIx i)
toBounds sz = (MIx { row = 1, col = 1 }, MIx { row = rows sz, col = cols sz })

-- | Type of matrix indices (row, column).

data MIx i = MIx { row, col :: i }
  deriving (Eq, Show, Ix, Ord)

instance (Arbitrary i, Integral i) => Arbitrary (MIx i) where
  arbitrary = do
    r <- positive
    c <- positive
    return $ MIx { row = r, col = c }

instance CoArbitrary i => CoArbitrary (MIx i) where
  coarbitrary (MIx r c) = coarbitrary r . coarbitrary c

-- | No nonpositive indices are allowed.

mIxInvariant :: (Ord i, Num i) => MIx i -> Bool
mIxInvariant i = row i >= 1 && col i >= 1

prop_Arbitrary_MIx :: MIx Integer -> Bool
prop_Arbitrary_MIx = mIxInvariant

-- | Type of matrices, parameterised on the type of values.

newtype Matrix i b = M { unM :: Array (MIx i) b }
  deriving (Eq, Ord, Functor)

matrixInvariant :: (Num i, Ix i) => Matrix i b -> Bool
matrixInvariant m =
  fst (bounds $ unM m) == MIx 1 1
  &&
  sizeInvariant (size m)

instance (Ix i, Num i, Enum i, Show i, Show b) => Show (Matrix i b) where
  showsPrec _ m =
    showString "Agda.Termination.Matrix.fromLists " . shows (size m) .
    showString " " . shows (toLists m)

instance (Arbitrary i, Num i, Integral i, Ix i, Arbitrary b)
         => Arbitrary (Matrix i b) where
  arbitrary     = matrix =<< arbitrary

instance (Ix i, Num i, Enum i, CoArbitrary b) => CoArbitrary (Matrix i b) where
  coarbitrary m = coarbitrary (toLists m)

prop_Arbitrary_Matrix :: TM -> Bool
prop_Arbitrary_Matrix = matrixInvariant

------------------------------------------------------------------------
-- Generating and creating matrices

-- | Generates a matrix of the given size, using the given generator
-- to generate the rows.

matrixUsingRowGen :: (Arbitrary i, Integral i, Ix i, Arbitrary b)
  => Size i
  -> (i -> Gen [b])
     -- ^ The generator is parameterised on the size of the row.
  -> Gen (Matrix i b)
matrixUsingRowGen sz rowGen = do
  rows <- vectorOf (fromIntegral $ rows sz) (rowGen $ cols sz)
  return $ fromLists sz rows

-- | Generates a matrix of the given size.

matrix :: (Arbitrary i, Integral i, Ix i, Arbitrary b)
  => Size i -> Gen (Matrix i b)
matrix sz = matrixUsingRowGen sz (\n -> vectorOf (fromIntegral n) arbitrary)

prop_matrix sz = forAll (matrix sz :: Gen TM) $ \m ->
  matrixInvariant m &&
  size m == sz

-- | Constructs a matrix from a list of (index, value)-pairs.

fromIndexList :: (Num i, Ix i) => Size i -> [(MIx i, b)] -> Matrix i b
fromIndexList sz = M . array (toBounds sz)

prop_fromIndexList :: TM -> Bool
prop_fromIndexList m = matrixInvariant m' && m' == m
  where vs = assocs $ unM m
        m' = fromIndexList (size m) vs

-- | @'fromLists' sz rs@ constructs a matrix from a list of lists of
-- values (a list of rows).
--
-- Precondition: @'length' rs '==' 'rows' sz '&&' 'all' (('==' 'cols' sz) . 'length') rs@.

fromLists :: (Num i, Ix i) => Size i -> [[b]] -> Matrix i b
fromLists sz bs = fromIndexList sz $ zip (range $ toBounds sz) (concat bs)

-- | Converts a matrix to a list of row lists.

toLists :: (Ix i, Num i, Enum i) => Matrix i b -> [[b]]
toLists m = [ [unM m ! MIx { row = r, col = c }
            | c <- [1 .. cols sz] ] | r <- [1 .. rows sz] ]
  where sz = size m

prop_fromLists_toLists :: TM -> Bool
prop_fromLists_toLists m = fromLists (size m) (toLists m) == m

------------------------------------------------------------------------
-- Combining and querying matrices

-- | The size of a matrix.

size :: Ix i => Matrix i b -> Size i
size m = Size { rows = row b, cols = col b }
  where (_, b) = bounds $ unM m

prop_size :: TM -> Bool
prop_size m = sizeInvariant (size m)

prop_size_fromIndexList :: Size Int -> Bool
prop_size_fromIndexList sz =
  size (fromIndexList sz ([] :: [(MIx Int, Integer)])) == sz

-- | 'True' iff the matrix is square.

square :: Ix i => Matrix i b -> Bool
square m = rows (size m) == cols (size m)

-- | Returns 'True' iff the matrix is empty.

isEmpty :: (Num i, Ix i) => Matrix i b -> Bool
isEmpty m = rows sz <= 0 || cols sz <= 0
  where sz = size m

-- | @'add' (+) m1 m2@ adds @m1@ and @m2@. Uses @(+)@ to add values.
--
-- Precondition: @'size' m1 == 'size' m2@.

add :: (Ix i, Num i)
    => (a -> b -> c) -> Matrix i a -> Matrix i b -> Matrix i c
add (+) m1 m2 =
  fromIndexList (size m1)
                [ (i, (unM m1 ! i) + (unM m2 ! i))
                | i <- range $ toBounds $ size m1 ]

prop_add sz =
  forAll (three (matrix sz :: Gen TM)) $ \(m1, m2, m3) ->
    let m' = add (+) m1 m2 in
      associative (add (+)) m1 m2 m3 &&
      commutative (add (+)) m1 m2 &&
      matrixInvariant m' &&
      size m' == size m1

-- | @'mul' m1 m2@ multiplies @m1@ and @m2@. Uses the operations of
-- the semiring to perform the multiplication.
--
-- Precondition: @'cols' ('size' m1) == rows ('size' m2)@.


mul :: (Enum i, Num i, Ix i)
    => Semiring a -> Matrix i a -> Matrix i a -> Matrix i a
mul semiring m1 m2 =
  fromIndexList sz' [ (ix, res)
                    | r <- [1 .. rows $ size m1]
                    , c <- [1 .. cols $ size m2]
                    , let ix = MIx { row = r, col = c }
                    , let res = mulRowCol r c
                    ]
    where
    sz' = Size { rows = rows $ size m1, cols = cols $ size m2 }

    mulRowCol r c =
      foldl' (Semiring.add semiring) (Semiring.zero semiring)
             [ (Semiring.mul semiring)
               (unM m1 ! MIx { row = r, col = i })
               (unM m2 ! MIx { row = i, col = c })
             | i <- [1 .. cols (size m1)]]

prop_mul sz =
  sized $ \n -> resize (n `div` 2) $
  forAll (two natural) $ \(c2, c3) ->
  forAll (matrix sz :: Gen TM) $ \m1 ->
  forAll (matrix (Size { rows = cols sz, cols = c2 })) $ \m2 ->
  forAll (matrix (Size { rows = c2, cols = c3 })) $ \m3 ->
    let m' = mult m1 m2 in
      associative mult m1 m2 m3 &&
      matrixInvariant m' &&
      size m' == Size { rows = rows sz, cols = c2 }
  where mult = mul Semiring.integerSemiring

-- | @'diagonal' m@ extracts the diagonal of @m@.
--
-- Precondition: @'square' m@.

diagonal :: (Enum i, Num i, Ix i) => Matrix i b -> Array i b
diagonal m = listArray (1, rows sz) [ unM m ! MIx {row = i, col = i}
                                    | i <- [1 .. rows sz] ]
  where sz = size m

prop_diagonal =
  forAll natural $ \n ->
  forAll (matrix (Size n n) :: Gen TM) $ \m ->
    bounds (diagonal m) == (1, n)

------------------------------------------------------------------------
-- Modifying matrices

-- | @'addColumn' x m@ adds a new column to @m@, after the columns
-- already existing in the matrix. All elements in the new column get
-- set to @x@.

addColumn :: (Ix i, Num i, Enum i) => b -> Matrix i b -> Matrix i b
addColumn x m = fromLists sz . addCol' . toLists $ m
  where
  sz      = (size m) { cols = cols (size m) + 1 }
  addCol' = map (++ [x])

prop_addColumn :: Integer -> TM -> Bool
prop_addColumn x m =
  matrixInvariant m'
  &&
  map init (toLists m') == toLists m
  where
  m' = addColumn x m

-- | @'addRow' x m@ adds a new row to @m@, after the rows already
-- existing in the matrix. All elements in the new row get set to @x@.

addRow :: (Ix i, Integral i) => b -> Matrix i b -> Matrix i b
addRow x m = fromLists sz . addRow' . toLists $ m
  where
  sz      = (size m) { rows = rows (size m) + 1 }
  addRow' = (++ [genericReplicate (cols (size m)) x])

prop_addRow :: Integer -> TM -> Bool
prop_addRow x m =
  matrixInvariant m'
  &&
  init (toLists m') == toLists m
  where
  m' = addRow x m

------------------------------------------------------------------------
-- Zipping (assumes non-empty matrices)

zipWith :: (a -> b -> c) ->
           Matrix Integer a -> Matrix Integer b -> Matrix Integer c
zipWith f m1 m2
  = fromLists (Size { rows = toInteger $ length ll,
                      cols = toInteger $ length (head ll) }) ll
    where ll = List.zipWith (List.zipWith f) (toLists m1) (toLists m2)


------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Termination.Matrix"
  [ quickCheck' prop_Arbitrary_Size
  , quickCheck' prop_Arbitrary_Matrix
  , quickCheck' prop_Arbitrary_MIx
  , quickCheck' prop_fromIndexList
  , quickCheck' prop_matrix
  , quickCheck' prop_size
  , quickCheck' prop_size_fromIndexList
  , quickCheck' prop_fromLists_toLists
  , quickCheck' prop_add
  , quickCheck' prop_mul
  , quickCheck' prop_diagonal
  , quickCheck' prop_addColumn
  , quickCheck' prop_addRow
  ]
