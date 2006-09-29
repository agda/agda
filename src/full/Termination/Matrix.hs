-- | Naive implementation of simple matrix library.

module Termination.Matrix
  ( Matrix
  , Index
  , Size(..)
  , matrix
  , size
  , fromList
  , toList
  , isEmpty
  , add
  ) where

import Data.Array
import Data.List
import Test.QuickCheck
import Termination.TestHelpers

-- | Type used for the matrix indices.

type Index = Int

-- | Size of a matrix.

data Size = Size { rows :: Index, cols :: Index }
  deriving (Eq, Show)

sizeInvariant :: Size -> Bool
sizeInvariant sz = rows sz >= 0 && cols sz >= 0

instance Arbitrary Size where
  arbitrary = do
    (r, c) <- two natural
    return $ Size { rows = r, cols = c }
    where natural = fmap abs arbitrary

  coarbitrary (Size rs cs) = coarbitrary rs . coarbitrary cs

prop_Arbitrary_size = sizeInvariant

-- | Converts a size to a set of bounds suitable for use with
-- the matrices in this module.

toBounds :: Size -> (MIx, MIx)
toBounds sz = ((1, 1), (rows sz, cols sz))

-- | Type of matrix indices (row, column).

type MIx = (Index, Index)

-- | Type of matrices, parameterised on the type of values.

newtype Matrix b = M { unM :: Array MIx b }
  deriving Eq

matrixInvariant :: Matrix b -> Bool
matrixInvariant m =
  fst (bounds $ unM m) == (1, 1)
  &&
  sizeInvariant (size m)

instance Show b => Show (Matrix b) where
  showsPrec _ m =
    showString "Termination.Matrix.fromList " . shows (toList m)

instance Arbitrary b => Arbitrary (Matrix b) where
  arbitrary = do
    sz <- arbitrary
    let colGen = sequence $ genericReplicate (cols sz) arbitrary
    rows <- sequence $ genericReplicate (rows sz) colGen
    return $ fromList sz rows

  coarbitrary m = coarbitrary (toList m)

prop_Arbitrary_matrix = matrixInvariant

-- | Constructs a matrix from a list of (index, value)-pairs.

matrix :: Size -> [(MIx, b)] -> Matrix b
matrix sz = M . array (toBounds sz)

prop_matrix :: Matrix Integer -> Bool
prop_matrix m = matrixInvariant m' && m' == m
  where vs = assocs $ unM m
        m' = matrix (size m) vs

-- | The size of a matrix.

size :: Matrix b -> Size
size m = Size { rows = r, cols = c }
  where (_, (r, c)) = bounds $ unM m

prop_size :: Matrix Integer -> Bool
prop_size m = sizeInvariant (size m)

prop_size_matrix :: Size -> [(MIx, Integer)] -> Bool
prop_size_matrix sz vs = size (matrix sz vs) == sz

-- | @'fromList' sz rows@ constructs a matrix from a list of lists of
-- values (a list of rows).
--
-- Precondition: @'length' rows = 'fst' sz '&&' 'all' (('==' 'snd' sz) . 'length') rows@.

fromList :: Size -> [[b]] -> Matrix b
fromList sz bs = matrix sz $ zip (range $ toBounds sz) (concat bs)

-- | Converts a matrix to a list of row lists.

toList :: Matrix b -> [[b]]
toList m = [ [unM m ! (r, c) | c <- [1 .. cols sz] ] | r <- [1 .. rows sz] ]
  where sz = size m

prop_fromList_toList :: Matrix Integer -> Bool
prop_fromList_toList m = fromList (size m) (toList m) == m

-- | Returns 'True' iff the matrix is empty.

isEmpty :: Matrix b -> Bool
isEmpty m = rows sz <= 0 || cols sz <= 0
  where sz = size m

-- | Adds two matrices. Uses the binary operation to add values.

add :: (a -> b -> c) -> Matrix a -> Matrix b -> Matrix c
add (+) m1 m2 =
  matrix (size m1)
         [ (i, (unM m1 ! i) + (unM m2 ! i))
         | i <- range $ toBounds $ size m1 ]

prop_add :: Matrix Integer -> Matrix Integer -> Matrix Integer -> Bool
prop_add m1 m2 m3 =
  associative (add (+)) m1 m2 m3 &&
  commutative (add (+)) m1 m2 &&
  matrixInvariant (add (+) m1 m2)

{-

multMatrix :: (a -> b -> c) -> (c -> c -> c) -> Matrix a -> Matrix b -> Matrix c
multMatrix t p m1 m2 = matrix (mr1,mc2) [((r,c),res) | r <- [1..mr1] , c <- [1..mc2], let res = multiply t p mc1 r c m1 m2 ]
          where 
                (mr1,mc1) = sizeMatrix m1
                (mr2,mc2) = sizeMatrix m2
                multiply :: (a -> b -> c) -> (c -> c -> c)-> Int -> Int -> Int -> Matrix a -> Matrix b -> c
                multiply t p size r c m1 m2 =
                      foldl1 p [ t (m1!(r,i)) (m2!(i,c)) | i <- [1..size]]


diagonal :: Matrix b -> Array Int b
diagonal m = array (1,r)  [(i,m!(i,i)) | i <-[1..r]]
      where    (r,_) = sizeMatrix m
                
printMatrix :: Show b => Matrix b -> String 
printMatrix m 
  | r < 1 || c < 1 = "[]"
  | otherwise = unlines [ printRow i c m | i <- range (1,r)]
          where printRow :: Show b => Int -> Int -> Matrix b -> String
                printRow r mc m = unwords [show (m ! (r,j)) | j <- range (1,mc)]
                (r,c) = sizeMatrix m


{-
list1,list2,list3 :: [[Int]]
list1 = [[1,2,3],[0,2,4]]
list2 = [[0,2,4],[1,2,3]]
list3 = [[1,3],[0,5],[1,1]]


mat1,mat2,mat3 :: Matrix Int
mat1 = listMatrix (2,3) list1

mat2 = listMatrix (2,3) list2

mat3 = addMatrix (+) mat1 mat2

mat4,mat6 :: Matrix Int
mat4 = listMatrix (3,2) list3

--mat5 = listMatrix (2,3) (list2 ++ list1)

mat6 = multMatrix (*) (+) mat2 mat4

res4 = printMatrix (2,3) mat2

res5 = printMatrix (3,2) mat4

res6 = printMatrix (2,2) mat6



-}
-}