{-# LANGUAGE CPP #-}

module InternalTests.Termination.SparseMatrix
  ( matrix
  , tests
  ) where

import Agda.Termination.Semiring (HasZero(..), Semiring)
import qualified Agda.Termination.Semiring as Semiring
import Agda.Termination.SparseMatrix
import Agda.Utils.Functor
import Agda.Utils.Tuple

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<*>) )
#endif

import Data.Array
import Data.Function
import qualified Data.List as List

import InternalTests.Helpers

------------------------------------------------------------------------
-- * Generators, properties and tests
------------------------------------------------------------------------

-- ** Size
------------------------------------------------------------------------

instance Integral i => Arbitrary (Size i) where
  arbitrary = do
    r <- natural
    c <- natural
    return $ Size { rows = fromInteger r, cols = fromInteger c }

instance CoArbitrary i => CoArbitrary (Size i) where
  coarbitrary (Size rs cs) = coarbitrary rs . coarbitrary cs

-- | Size invariant: dimensions are non-negative.

sizeInvariant :: (Ord i, Num i) => Size i -> Bool
sizeInvariant sz = rows sz >= 0 && cols sz >= 0

prop_Arbitrary_Size :: Size Integer -> Bool
prop_Arbitrary_Size = sizeInvariant

prop_size :: TM -> Bool
prop_size m = sizeInvariant (size m)

-- ** Matrix indices
------------------------------------------------------------------------

instance Integral i => Arbitrary (MIx i) where
  arbitrary = MIx <$> positive <*> positive

instance CoArbitrary i => CoArbitrary (MIx i) where
  coarbitrary (MIx r c) = coarbitrary r . coarbitrary c

-- | Indices must be positive, @>= 1@.

mIxInvariant :: (Ord i, Num i) => MIx i -> Bool
mIxInvariant i = row i >= 1 && col i >= 1

prop_Arbitrary_MIx :: MIx Integer -> Bool
prop_Arbitrary_MIx = mIxInvariant

-- ** Matrices
------------------------------------------------------------------------

-- | Matrix indices are lexicographically sorted with no duplicates.
--   All indices must be within bounds.
matrixInvariant :: (Num i, Ix i, HasZero b) => Matrix i b -> Bool
matrixInvariant (Matrix size@Size{ rows, cols} m) =
  sizeInvariant size
  && all inBounds m
  && all nonZero  m
  && strictlySorted (MIx 0 0) m
  where
    inBounds (MIx i j, _) = 1 <= i && i <= rows
                         && 1 <= j && j <= cols
    nonZero (_, b) = b /= zeroElement

-- | Check whether an association list is ordered and
--   deterministic, a partial function from @i@ to @b@.
strictlySorted :: (Ord i) => i -> [(i, b)] -> Bool
strictlySorted i []            = True
strictlySorted i ((i', _) : l) = i < i' && strictlySorted i' l
-- Ord MIx should be the lexicographic order already (Haskell report).

-- | Generates a matrix of the given size, using the given generator
-- to generate the rows.

matrixUsingRowGen :: (Integral i, HasZero b)
  => Size i
  -> (i -> Gen [b])
     -- ^ The generator is parameterised on the size of the row.
  -> Gen (Matrix i b)
matrixUsingRowGen sz rowGen = do
  rows <- vectorOf (fromIntegral $ rows sz) (rowGen $ cols sz)
  return $ fromLists sz rows

-- | Generates a matrix of the given size.

matrix :: (Integral i, Arbitrary b, HasZero b)
       => Size i -> Gen (Matrix i b)
matrix sz = matrixUsingRowGen sz (\n -> vectorOf (fromIntegral n) arbitrary)

prop_matrix :: Size Int -> Property
prop_matrix sz = forAll (matrix sz :: Gen TM) $ \ m -> size m == sz

-- | Generate a matrix of arbitrary size.

instance (Integral i, Arbitrary b, HasZero b)
         => Arbitrary (Matrix i b) where
  arbitrary     = matrix =<< arbitrary

instance (Integral i, CoArbitrary b, HasZero b) => CoArbitrary (Matrix i b) where
  coarbitrary m = coarbitrary (toLists m)

-- | This matrix type is used for tests.

type TM = Matrix Int Int

prop_Arbitrary_Matrix :: TM -> Bool
prop_Arbitrary_Matrix = matrixInvariant

-- ** Matrix operations

-- | 'fromIndexList' is identity on well-formed sparse matrices.

prop_fromIndexList :: TM -> Bool
prop_fromIndexList m@(Matrix size vs) = fromIndexList size vs == m

-- | Converting a matrix to a list of lists and back is the identity.

prop_fromLists_toLists :: TM -> Bool
prop_fromLists_toLists m = fromLists (size m) (toLists m) == m

-- | Any 1x1 matrix is a singleton.

prop_isSingleton :: Int -> Bool
prop_isSingleton b = Just b == (isSingleton (fromLists (Size 1 1) [[b]] :: TM))

-- | The length of the diagonal is the minimum of the number of
--   rows and columns of the matrix.

prop_diagonal :: TM -> Bool
prop_diagonal m@(Matrix (Size r c) _) =
    length (diagonal m) == min r c

-- prop_diagonal' n =
--   forAll natural $ \n ->
--   forAll (matrix (Size n n) :: Gen TM) $ \m ->
--     length (diagonal m) == n

-- | Transposing twice is the identity.

prop_transpose :: TM -> Bool
prop_transpose m = matrixInvariant m' && m == transpose m'
  where m' = transpose m

-- | Verify 'toSparseRows' against an alternative implementation which
-- serves as specification.

toSparseRows' :: (Eq i) => Matrix i b -> [(i,[(i,b)])]
toSparseRows' (Matrix _ m) =
  -- group list by row index
  for (List.groupBy ((==) `on` (row . fst)) m) $ \ ((MIx i j, b) : vs) ->
  -- turn each group into a sparse row
    (i, (j,b) : map (mapFst col) vs)

prop_toSparseRows :: TM -> Bool
prop_toSparseRows m = toSparseRows m == toSparseRows' m

prop_addColumn :: TM -> Bool
prop_addColumn m =
  matrixInvariant m'
  &&
  map init (toLists m') == toLists m
  where
  m' = addColumn zeroElement m


prop_addRow :: TM -> Bool
prop_addRow m =
  matrixInvariant m'
  &&
  init (toLists m') == toLists m
  where
  m' = addRow zeroElement m


-- ** Matrix addition


-- | Old implementation of 'zipMatrices'.

zipMatrices' :: forall a b c i . (Ord i)
  => (a -> c)       -- ^ Element only present in left matrix.
  -> (b -> c)       -- ^ Element only present in right matrix.
  -> (a -> b -> c)  -- ^ Element present in both matrices.
  -> (c -> Bool)    -- ^ Result counts as zero?
  -> Matrix i a -> Matrix i b -> Matrix i c
zipMatrices' f g h zero m1 m2 = Matrix (supSize m1 m2) (merge (unM m1) (unM m2))
  where
    merge :: [(MIx i,a)] -> [(MIx i,b)] -> [(MIx i,c)]
    merge [] m2 = filter (not . zero . snd) $ map (mapSnd g) m2
    merge m1 [] = filter (not . zero . snd) $ map (mapSnd f) m1
    merge m1@((i,a):m1') m2@((j,b):m2') =
      case compare i j of
        LT -> if zero c then r else (i,c) : r where c = f a   ; r = merge m1' m2
        GT -> if zero c then r else (j,c) : r where c = g b   ; r = merge m1  m2'
        EQ -> if zero c then r else (i,c) : r where c = h a b ; r = merge m1' m2'

-- | Verify 'zipMatrices' against older implementation

prop_zipMatrices_correct :: TM -> TM -> Bool
prop_zipMatrices_correct m1 m2 =
  zipMatrices id id (+) (== 0) m1 m2 == zipMatrices' id id (+) (== 0) m1 m2


-- | Matrix addition is well-defined, associative and commutative.

prop_add :: Size Int -> Property
prop_add sz =
  forAll (three (matrix sz :: Gen TM)) $ \(m1, m2, m3) ->
    let m' = add (+) m1 m2 in
      isAssociative (add (+)) m1 m2 m3 &&
      isCommutative (add (+)) m1 m2 &&
      matrixInvariant m' &&
      size m' == size m1

-- | Verify addition against an older implementation.
--
--   The older implementation did not fully preserve sparsity,
--   i.e., introduced zeros.  Thus, we need to convert to lists to
--   obtain equal results.

prop_add_correct :: TM -> TM -> Bool
prop_add_correct m1 m2 = toLists (add (+) m1 m2) == toLists (add' (+) m1 m2)
  where
    add' :: (Ord i) => (a -> a -> a) -> Matrix i a -> Matrix i a -> Matrix i a
    add' plus m1 m2 = Matrix (supSize m1 m2) $ mergeAssocWith plus (unM m1) (unM m2)
      where
        mergeAssocWith :: (Ord i) => (a -> a -> a) -> [(i,a)] -> [(i,a)] -> [(i,a)]
        mergeAssocWith f [] m = m
        mergeAssocWith f l [] = l
        mergeAssocWith f l@((i,a):l') m@((j,b):m')
            | i < j = (i,a) : mergeAssocWith f l' m
            | i > j = (j,b) : mergeAssocWith f l m'
            | otherwise = (i, f a b) : mergeAssocWith f l' m'

-- ** Matrix multiplication

-- | Specification of 'interAssocWith'.

interAssocWith' :: (Eq i) => (a -> a -> a) -> [(i,a)] -> [(i,a)] -> [(i,a)]
interAssocWith' f l l' = [ (i, f a b) | (i,a) <- l, (j,b) <- l', i == j ]

-- | Efficient implementation of 'interAssocWith' matches its specification.

prop_interAssocWith_correct :: [(Int,Int)] -> [(Int,Int)] -> Bool
prop_interAssocWith_correct xs ys =
  interAssocWith (*) l l' == interAssocWith' (*) l l'
  where
    l  = List.sortBy (compare `on` fst) xs
    l' = List.sortBy (compare `on` fst) ys

interAssocWith2 :: Ord i => (a -> a -> a) -> [(i,a)] -> [(i,a)] -> [(i,a)]
interAssocWith2 f = zipAssocWith (const []) (const []) (const Nothing) (const Nothing) (\ a -> Just . f a)

prop_interAssocWith_correct2 :: [(Int,Int)] -> [(Int,Int)] -> Bool
prop_interAssocWith_correct2 xs ys =
  interAssocWith (*) xs ys == interAssocWith2 (*) xs ys
  where
    l  = List.sortBy (compare `on` fst) xs
    l' = List.sortBy (compare `on` fst) ys

-- | Matrix multiplication is well-defined and associative.

prop_mul :: Size Int -> Property
prop_mul sz =
  mapSize (`div` 2) $
  forAll (two natural) $ \(c2, c3) ->
  forAll (matrix sz :: Gen TM) $ \m1 ->
  forAll (matrix (Size { rows = cols sz, cols = c2 })) $ \m2 ->
  forAll (matrix (Size { rows = c2, cols = c3 })) $ \m3 ->
    let m' = mult m1 m2 in
      isAssociative mult m1 m2 m3 &&
      matrixInvariant m' &&
      size m' == Size { rows = rows sz, cols = c2 }
  where mult = mul Semiring.intSemiring

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "InternalTests.Termination.SparseMatrix"
  [ quickCheck' prop_transpose
  , quickCheck' prop_Arbitrary_Size
  , quickCheck' prop_Arbitrary_Matrix
  , quickCheck' prop_Arbitrary_MIx
  , quickCheck' prop_fromIndexList
  , quickCheck' prop_matrix
  , quickCheck' prop_size
  , quickCheck' prop_toSparseRows
  , quickCheck' prop_fromLists_toLists
  , quickCheck' prop_isSingleton
  , quickCheck' prop_zipMatrices_correct
  , quickCheck' prop_add
  , quickCheck' prop_add_correct
  , quickCheck' prop_mul
  , quickCheck' prop_diagonal
  , quickCheck' prop_addColumn
  , quickCheck' prop_addRow
  ]
