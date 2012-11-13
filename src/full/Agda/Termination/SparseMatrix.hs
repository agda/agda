{-# LANGUAGE CPP, DeriveFunctor #-}

{- | Sparse matrices.

We assume the matrices to be very sparse, so we just implement them as
sorted association lists.

 -}

module Agda.Termination.SparseMatrix
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
--  , Agda.Termination.Matrix.zipWith
  , matrix
  , matrixUsingRowGen
    -- * Combining and querying matrices
  , size
  , square
  , isEmpty
  , isSingleton
  , add, intersectWith
  , mul
  , transpose
  , diagonal
    -- * Modifying matrices
  , addRow
  , addColumn
    -- * Tests
  , Agda.Termination.SparseMatrix.tests
  ) where

import Data.Array
import qualified Data.List as List
import Data.Maybe
import Data.Monoid

import Agda.Utils.Pretty hiding (isEmpty)
import Agda.Utils.QuickCheck
import Agda.Utils.TestHelpers
import Agda.Termination.Semiring (HasZero(..), SemiRing, Semiring)
import qualified Agda.Termination.Semiring as Semiring

#include "../undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- Basic data types

-- | This matrix type is used for tests.

type TM = Matrix Integer Integer

-- | Size of a matrix.

data Size i = Size { rows :: i, cols :: i }
  deriving (Eq, Ord, Show)

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

data Matrix i b = M { size :: Size i, unM :: [(MIx i, b)] }
  deriving (Eq, Ord, Functor)

matrixInvariant :: (Num i, Ix i) => Matrix i b -> Bool
matrixInvariant m = all (\ (MIx i j, b) -> 1 <= i && i <= rows sz
                                        && 1 <= j && j <= cols sz) (unM m)
  && strictlySorted (MIx 0 0) (unM m)
  && sizeInvariant sz
  where sz = size m

-- matrix indices are lexicographically sorted with no duplicates
-- Ord MIx should be the lexicographic one already (Haskell report)

strictlySorted :: (Ord i) => i -> [(i, b)] -> Bool
strictlySorted i [] = True
strictlySorted i ((i', b) : l) = i < i' && strictlySorted i' l
{-
strictlySorted (MIx i j) [] = True
strictlySorted (MIx i j) ((MIx i' j', b) : l) =
  (i < i' || i == i' &&  j < j' ) && strictlySorted (MIx i' j') b
-}

instance (Ord i, Integral i, Enum i, Ix i, Show i, Show b, HasZero b) => Show (Matrix i b) where
  showsPrec _ m =
    showString "Agda.Termination.Matrix.fromLists " . shows (size m) .
    showString " " . shows (toLists m)

instance (Show i, Integral i, Ix i, HasZero b, Pretty b) =>
         Pretty (Matrix i b) where
  pretty = vcat . map (hsep . map pretty) . toLists

instance (Arbitrary i, Num i, Integral i, Arbitrary b, HasZero b)
         => Arbitrary (Matrix i b) where
  arbitrary     = matrix =<< arbitrary

instance (Show i, Ord i, Integral i, Enum i, Ix i, CoArbitrary b, HasZero b) => CoArbitrary (Matrix i b) where
  coarbitrary m = coarbitrary (toLists m)


prop_Arbitrary_Matrix :: TM -> Bool
prop_Arbitrary_Matrix = matrixInvariant


------------------------------------------------------------------------
-- Generating and creating matrices

-- | Generates a matrix of the given size, using the given generator
-- to generate the rows.

matrixUsingRowGen :: (Arbitrary i, Integral i, Arbitrary b, HasZero b)
  => Size i
  -> (i -> Gen [b])
     -- ^ The generator is parameterised on the size of the row.
  -> Gen (Matrix i b)
matrixUsingRowGen sz rowGen = do
  rows <- vectorOf (fromIntegral $ rows sz) (rowGen $ cols sz)
  return $ fromLists sz rows

-- | Generates a matrix of the given size.

matrix :: (Arbitrary i, Integral i, Arbitrary b, HasZero b)
  => Size i -> Gen (Matrix i b)
matrix sz = matrixUsingRowGen sz (\n -> vectorOf (fromIntegral n) arbitrary)

prop_matrix sz = forAll (matrix sz :: Gen TM) $ \m ->
--  matrixInvariant m &&
  size m == sz

-- | Constructs a matrix from a list of (index, value)-pairs.

-- compareElt = (\ (i,_) (j,_) -> compare i j)
-- normalize = filter (\ (i,b) -> b /= zeroElement)

fromIndexList :: (Ord i, HasZero b) => Size i -> [(MIx i, b)] -> Matrix i b
fromIndexList sz = M sz . List.sortBy (\ (i,_) (j,_) -> compare i j) . filter (\ (i,b) -> b /= zeroElement)

prop_fromIndexList :: TM -> Bool
prop_fromIndexList m = matrixInvariant m' && m' == m
  where vs = unM m
        m' = fromIndexList (size m) vs

-- | @'fromLists' sz rs@ constructs a matrix from a list of lists of
-- values (a list of rows).
--
-- Precondition: @'length' rs '==' 'rows' sz '&&' 'all' (('==' 'cols' sz) . 'length') rs@.

fromLists :: (Ord i, Num i, Enum i, HasZero b) => Size i -> [[b]] -> Matrix i b
fromLists sz bs = fromIndexList sz $ zip ([ MIx i j | i <- [1..rows sz]
                                                    , j <- [1..cols sz]]) (concat bs)

-- | Converts a sparse matrix to a sparse list of rows

toSparseRows :: (Eq i, Num i, Enum i) => Matrix i b -> [(i,[(i,b)])]
toSparseRows m = aux 1 [] (unM m)
  where aux i' [] []  = []
        aux i' row [] = [(i', reverse row)]
        aux i' row ((MIx i j, b) : m)
            | i' == i   = aux i' ((j,b):row) m
            | otherwise = (i', reverse row) : aux i [(j,b)] m

-- sparse vectors cannot have two entries in one column
blowUpSparseVec :: (Show i, Ord i, Num i, Enum i) => b -> i -> [(i,b)] -> [b]
blowUpSparseVec zero n l = aux 1 l
  where aux i [] | i > n = []
                 | otherwise = zero : aux (i+1) []
        aux i ((j,b):l) | i <= n && j == i = b : aux (succ i) l
        aux i ((j,b):l) | i <= n && j >= i = zero : aux (succ i) ((j,b):l)
        aux i l = __IMPOSSIBLE__
          -- error $ "blowUpSparseVec (n = " ++ show n ++ ") aux i=" ++ show i ++ " j=" ++ show (fst (head l)) ++ " length l = " ++ show (length l)

-- | Converts a matrix to a list of row lists.

toLists :: (Show i, Ord i, Integral i, Enum i, Ix i, HasZero b) => Matrix i b -> [[b]]
toLists m = -- if not $ matrixInvariant m then __IMPOSSIBLE__ else
    blowUpSparseVec emptyRow nr $
      map (\ (i,r) -> (i, blowUpSparseVec zeroElement nc r)) $ toSparseRows m
  where
    sz = size m
    nr = rows sz
    nc = cols sz
    emptyRow = take (fromIntegral nc) $ repeat zeroElement

prop_fromLists_toLists :: TM -> Bool
prop_fromLists_toLists m = fromLists (size m) (toLists m) == m

------------------------------------------------------------------------
-- Combining and querying matrices

-- | The size of a matrix.

{-
size :: Ix i => Matrix i b -> Size i
size m = Size { rows = row b, cols = col b }
  where (_, b) = bounds $ unM m
-}

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

-- | Returns 'Just b' iff it is a 1x1 matrix with just one entry 'b'.

isSingleton :: (Num i, Ix i) => Matrix i b -> Maybe b
isSingleton m = if (rows sz == 1 || cols sz == 1) then
    case unM m of
      [(_,b)] -> Just b
      _ -> __IMPOSSIBLE__
  else Nothing
  where sz = size m

-- | Transposition
transposeSize (Size { rows = n, cols = m }) = Size { rows = m, cols = n }
transpose m = M { size = transposeSize (size m)
                , unM  = List.sortBy (\ (i,a) (j,b) -> compare i j) $
                           map (\(MIx i j, b) -> (MIx j i, b)) $ unM m }

prop_transpose :: TM -> Bool
prop_transpose m = matrixInvariant m' && m == transpose m'
  where m' = transpose m

-- | @'add' (+) m1 m2@ adds @m1@ and @m2@. Uses @(+)@ to add values.
--
-- No longer precondition: @'size' m1 == 'size' m2@.

add :: (Ord i) => (a -> a -> a) -> Matrix i a -> Matrix i a -> Matrix i a
add plus m1 m2 = M (supSize m1 m2) $ mergeAssocWith plus (unM m1) (unM m2)

-- | Compute the matrix size of the union of two matrices.
supSize m1 m2 = Size { rows = r, cols = c }
  where
    sz1 = size m1
    sz2 = size m2
    r   = max (rows sz1) (rows sz2)
    c   = max (cols sz1) (cols sz2)

-- | assoc list union
mergeAssocWith :: (Ord i) => (a -> a -> a) -> [(i,a)] -> [(i,a)] -> [(i,a)]
mergeAssocWith f [] m = m
mergeAssocWith f l [] = l
mergeAssocWith f l@((i,a):l') m@((j,b):m')
    | i < j = (i,a) : mergeAssocWith f l' m
    | i > j = (j,b) : mergeAssocWith f l m'
    | otherwise = (i, f a b) : mergeAssocWith f l' m'

-- | @'intersectWith' f m1 m2@ build the pointwise conjunction @m1@ and @m2@.
--   Uses @f@ to combine non-zero values.
--
-- No longer precondition: @'size' m1 == 'size' m2@.

intersectWith :: (Ord i) => (a -> a -> a) -> Matrix i a -> Matrix i a -> Matrix i a
intersectWith f m1 m2 = M (infSize m1 m2) $ interAssocWith f (unM m1) (unM m2)

-- | Compute the matrix size of the intersection of two matrices.
infSize m1 m2 = Size { rows = r, cols = c }
  where
    sz1 = size m1
    sz2 = size m2
    r   = min (rows sz1) (rows sz2)
    c   = min (cols sz1) (cols sz2)

-- | assoc list intersection
interAssocWith :: (Ord i) => (a -> a -> a) -> [(i,a)] -> [(i,a)] -> [(i,a)]
interAssocWith f [] m = []
interAssocWith f l [] = []
interAssocWith f l@((i,a):l') m@((j,b):m')
    | i < j = interAssocWith f l' m
    | i > j = interAssocWith f l m'
    | otherwise = (i, f a b) : interAssocWith f l' m'

prop_add sz =
  forAll (three (matrix sz :: Gen TM)) $ \(m1, m2, m3) ->
    let m' = add (+) m1 m2 in
      associative (add (+)) m1 m2 m3 &&
      commutative (add (+)) m1 m2 &&
      matrixInvariant m' &&
      size m' == size m1

-- | @'mul' semiring m1 m2@ multiplies @m1@ and @m2@. Uses the
-- operations of the semiring @semiring@ to perform the
-- multiplication.
--
-- Precondition: @'cols' ('size' m1) == rows ('size' m2)@.

{- mul A B works as follows:
* turn A into a list of sparse rows and the transposed B as well
* form the crossproduct using the inner vector product to compute els
* the inner vector product is summing up
  after intersecting with the muliplication op of the semiring
-}

mul :: (Enum i, Num i, Ix i, Eq a)
    => Semiring a -> Matrix i a -> Matrix i a -> Matrix i a
mul semiring m1 m2 = M (Size { rows = rows (size m1), cols = cols (size m2) }) $
  filter (\ (i,b) -> b /= Semiring.zero semiring) $
  [ (MIx i j, List.foldl' (Semiring.add semiring) (Semiring.zero semiring) $
                map snd $ interAssocWith (Semiring.mul semiring) v w)
    | (i,v) <- toSparseRows m1
    , (j,w) <- toSparseRows $ transpose m2 ]

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
-- No longer precondition: @'square' m@.

diagonal :: (Show i, Enum i, Num i, Ix i, HasZero b) => Matrix i b -> Array i b
diagonal m = -- if r /= c then __IMPOSSIBLE__ else  -- works also for non-square
  listArray (1, n) $ blowUpSparseVec zeroElement n $
    mapMaybe (\ ((MIx i j),b) -> if i==j then Just (i,b) else Nothing) $ unM m
--    map (\ ((MIx i j),b) -> (i,b)) $ filter (\ ((MIx i j),b) -> i==j) (unM m)
  where
    sz = size m
    r  = rows sz
    c  = cols sz
    n  = max r c

prop_diagonal =
  forAll natural $ \n ->
  forAll (matrix (Size n n) :: Gen TM) $ \m ->
    bounds (diagonal m) == (1, n)

------------------------------------------------------------------------
-- Modifying matrices

-- | @'addColumn' x m@ adds a new column to @m@, after the columns
-- already existing in the matrix. All elements in the new column get
-- set to @x@.

addColumn :: (Num i, HasZero b) => b -> Matrix i b -> Matrix i b
addColumn x m | x == zeroElement = m { size = (size m) { cols = cols (size m) + 1 }}
              | otherwise = __IMPOSSIBLE__

prop_addColumn :: TM -> Bool
prop_addColumn m =
  matrixInvariant m'
  &&
  map init (toLists m') == toLists m
  where
  m' = addColumn zeroElement m

-- | @'addRow' x m@ adds a new row to @m@, after the rows already
-- existing in the matrix. All elements in the new row get set to @x@.

addRow :: (Num i, HasZero b) => b -> Matrix i b -> Matrix i b
addRow x m | x == zeroElement = m { size = (size m) { rows = rows (size m) + 1 }}
           | otherwise = __IMPOSSIBLE__

prop_addRow :: TM -> Bool
prop_addRow m =
  matrixInvariant m'
  &&
  init (toLists m') == toLists m
  where
  m' = addRow zeroElement m

------------------------------------------------------------------------
-- Zipping (assumes non-empty matrices)

{- use mergeAssocList or interAssocList instead
zipWith :: (a -> b -> c) ->
           Matrix Integer a -> Matrix Integer b -> Matrix Integer c
zipWith f m1 m2
  = fromLists (Size { rows = toInteger $ length ll,
                      cols = toInteger $ length (head ll) }) ll
    where ll = List.zipWith (List.zipWith f) (toLists m1) (toLists m2)
-}

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Termination.Matrix"
  [ quickCheck' prop_transpose
  , quickCheck' prop_Arbitrary_Size
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
