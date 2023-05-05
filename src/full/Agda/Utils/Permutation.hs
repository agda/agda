
module Agda.Utils.Permutation where

import Prelude hiding (drop, null)

import Control.DeepSeq
import Control.Monad (filterM)

import Data.Array.Unboxed
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.Strict as IntMapS
import qualified Data.IntSet as IntSet
import Data.Functor.Identity
import qualified Data.List as List
import Data.Maybe

import GHC.Generics (Generic)

import Agda.Utils.Functor
import Agda.Utils.Null
import Agda.Utils.Size
import Agda.Utils.Tuple

import Agda.Utils.Impossible

-- | Partial permutations. Examples:
--
--   @permute [1,2,0]   [x0,x1,x2] = [x1,x2,x0]@     (proper permutation).
--
--   @permute [1,0]     [x0,x1,x2] = [x1,x0]@        (partial permuation).
--
--   @permute [1,0,1,2] [x0,x1,x2] = [x1,x0,x1,x2]@  (not a permutation because not invertible).
--
--   Agda typing would be:
--   @Perm : {m : Nat}(n : Nat) -> Vec (Fin n) m -> Permutation@
--   @m@ is the 'size' of the permutation.
data Permutation = Perm { permRange :: Int, permPicks :: [Int] }
  deriving (Eq, Generic)

instance Show Permutation where
  show (Perm n xs) = showx [0..n - 1] ++ " -> " ++ showx xs
    where showx = showList "," (\ i -> "x" ++ show i)
          showList :: String -> (a -> String) -> [a] -> String
          showList sep f [] = ""
          showList sep f [e] = f e
          showList sep f (e:es) = f e ++ sep ++ showList sep f es

instance Sized Permutation where
  size    (Perm _ xs) = size xs
  natSize (Perm _ xs) = natSize xs

instance Null Permutation where
  empty = Perm 0 []
  null (Perm _ picks) = null picks

instance NFData Permutation

-- | @permute [1,2,0] [x0,x1,x2] = [x1,x2,x0]@
--   More precisely, @permute indices list = sublist@, generates @sublist@
--   from @list@ by picking the elements of list as indicated by @indices@.
--   @permute [1,3,0] [x0,x1,x2,x3] = [x1,x3,x0]@
--
--   Agda typing:
--   @permute (Perm {m} n is) : Vec A m -> Vec A n@
--
-- Precondition for @'permute' ('Perm' _ is) xs@: Every index in @is@
-- must be non-negative and, if @xs@ is finite, then every index must
-- also be smaller than the length of @xs@.
--
-- The implementation is supposed to be extensionally equal to the
-- following one (if different exceptions are identified), but in some
-- cases more efficient:
-- @
--   permute ('Perm' _ is) xs = 'map' (xs 'Agda.Utils.List.!!') is
-- @
permute :: Permutation -> [a] -> [a]
permute (Perm _ is) xs = go mempty 0 xs is
  where
  -- Computes the list of permuted elements.
  go :: IntMap a  -- A map from positions to elements that have
                  -- already been seen.
     -> Int       -- The number of elements that have been seen (the
                  -- size of the map).
     -> [a]       -- Elements that have not yet been seen.
     -> [Int]     -- Indices to process.
     -> [a]
  go seen !n xs []       = []
  go seen  n xs (i : is)
    | i < n     = fromMaybe __IMPOSSIBLE__
                    (IntMap.lookup i seen) :
                  go seen n xs is
    | otherwise = scan seen n xs (i - n) is

  -- Finds the element at the given position and continues.
  scan :: IntMap a -> Int -> [a] -> Int -> [Int] -> [a]
  scan seen !n (x : xs) !i is
    | i == 0 = x : (go $! seen') n' xs is
    | i > 0  = (scan $! seen') n' xs (i - 1) is
    where
    seen' = IntMap.insert n x seen
    n'    = n + 1
  scan seen n xs !_ is = __IMPOSSIBLE__ : go seen n xs is

-- |  Invert a Permutation on a partial finite int map.
-- @inversePermute perm f = f'@
-- such that @permute perm f' = f@
--
-- Example, with map represented as @[Maybe a]@:
-- @
--   f    = [Nothing, Just a, Just b ]
--   perm = Perm 4 [3,0,2]
--   f'   = [ Just a , Nothing , Just b , Nothing ]
-- @
-- Zipping @perm@ with @f@ gives @[(0,a),(2,b)]@, after compression
-- with @catMaybes@.  This is an @IntMap@ which can easily
-- written out into a substitution again.

class InversePermute a b where
  inversePermute :: Permutation -> a -> b

instance InversePermute [Maybe a] [(Int,a)] where
  inversePermute (Perm n is) = catMaybes . zipWith (\ i ma -> (i,) <$> ma) is

instance InversePermute [Maybe a] (IntMap a) where
  inversePermute p = IntMap.fromList . inversePermute p

instance InversePermute [Maybe a] [Maybe a] where
  inversePermute p@(Perm n _) = tabulate . inversePermute p
    where tabulate m = for [0..n-1] $ \ i -> IntMap.lookup i m

instance InversePermute (Int -> a) [Maybe a] where
  inversePermute (Perm n xs) f =
    for [0..n-1] $ \i -> f <$> IntMap.lookup i m
    where
    m = IntMapS.fromListWith (flip const) $ zip xs [0..]

-- | Identity permutation.
idP :: Int -> Permutation
idP n = Perm n [0..n - 1]

-- | Restrict a permutation to work on @n@ elements, discarding picks @>=n@.
takeP :: Int -> Permutation -> Permutation
takeP n (Perm m xs) = Perm n $ filter (< n) xs

-- | Pick the elements that are not picked by the permutation.
droppedP :: Permutation -> Permutation
droppedP (Perm n xs) = Perm n $ filter (notInXs !) [0 .. n - 1]
  where
  notInXs :: UArray Int Bool
  notInXs =
    accumArray (flip const) True (0, n - 1) (zip xs (repeat False))

-- | @liftP k@ takes a @Perm {m} n@ to a @Perm {m+k} (n+k)@.
--   Analogous to 'Agda.TypeChecking.Substitution.liftS',
--   but Permutations operate on de Bruijn LEVELS, not indices.
liftP :: Int -> Permutation -> Permutation
liftP n (Perm m xs) = Perm (n + m) $ xs ++ [m..m+n-1]
-- liftP n (Perm m xs) = Perm (n + m) $ [0..n-1] ++ map (n+) xs -- WRONG, works for indices, but not for levels

-- | @permute (compose p1 p2) == permute p1 . permute p2@
composeP :: Permutation -> Permutation -> Permutation
composeP p1 (Perm n xs) = Perm n $ permute p1 xs
  {- proof:
      permute (compose (Perm xs) (Perm ys)) zs
      == permute (Perm (permute (Perm xs) ys)) zs
      == map (zs !!) (permute (Perm xs) ys)
      == map (zs !!) (map (ys !!) xs)
      == map (zs !! . ys !!) xs
      == map (\x -> zs !! (ys !! x)) xs
      == map (\x -> map (zs !!) ys !! x) xs  {- map f xs !! n == f (xs !! n) -}
      == map (map (zs !!) ys !!) xs
      == permute (Perm xs) (permute (Perm ys) zs)
  -}

-- | @invertP err p@ is the inverse of @p@ where defined,
--   otherwise defaults to @err@.
--   @composeP p (invertP err p) == p@
invertP :: Int -> Permutation -> Permutation
invertP err p@(Perm n xs) = Perm (size xs) $ elems tmpArray
  where
  -- This array cannot be unboxed, because it should be possible to
  -- instantiate err with __IMPOSSIBLE__.
  tmpArray :: Array Int Int
  tmpArray = accumArray (const id) err (0, n-1) $ zip xs [0..]

-- | Turn a possible non-surjective permutation into a surjective permutation.
compactP :: Permutation -> Permutation
compactP p@(Perm _ xs) = Perm (length xs) $ map adjust xs
  where
  missing      = IntSet.fromList $ permPicks $ droppedP p
  holesBelow k = IntSet.size $ fst $ IntSet.split k missing
  adjust k     = k - holesBelow k

-- | @permute (reverseP p) xs ==
--    reverse $ permute p $ reverse xs@
--
--   Example:
--   @
--        permute (reverseP (Perm 4 [1,3,0])) [x0,x1,x2,x3]
--     == permute (Perm 4 $ map (3-) [0,3,1]) [x0,x1,x2,x3]
--     == permute (Perm 4 [3,0,2]) [x0,x1,x2,x3]
--     == [x3,x0,x2]
--     == reverse [x2,x0,x3]
--     == reverse $ permute (Perm 4 [1,3,0]) [x3,x2,x1,x0]
--     == reverse $ permute (Perm 4 [1,3,0]) $ reverse [x0,x1,x2,x3]
--   @
--
--   With @reverseP@, you can convert a permutation on de Bruijn indices
--   to one on de Bruijn levels, and vice versa.
reverseP :: Permutation -> Permutation
reverseP (Perm n xs) = Perm n $ map ((n - 1) -) $ reverse xs
                  -- = flipP $ Perm n $ reverse xs

-- | @permPicks (flipP p) = permute p (downFrom (permRange p))@
--   or
--   @permute (flipP (Perm n xs)) [0..n-1] = permute (Perm n xs) (downFrom n)@
--
--   Can be use to turn a permutation from (de Bruijn) levels to levels
--   to one from levels to indices.
--
--   See 'Agda.Syntax.Internal.Patterns.numberPatVars'.
flipP :: Permutation -> Permutation
flipP (Perm n xs) = Perm n $ map (n - 1 -) xs

-- | @expandP i n π@ in the domain of @π@ replace the /i/th element by /n/ elements.
expandP :: Int -> Int -> Permutation -> Permutation
expandP i n (Perm m xs) = Perm (m + n - 1) $ concatMap expand xs
  where
    expand j
      | j == i    = [i..i + n - 1]
      | j < i     = [j]
      | otherwise = [j + n - 1]

-- | Stable topologic sort. The first argument decides whether its first
--   argument is an immediate parent to its second argument.
topoSort :: (a -> a -> Bool) -> [a] -> Maybe Permutation
topoSort parent xs = runIdentity $ topoSortM (\x y -> Identity $ parent x y) xs

topoSortM :: Monad m => (a -> a -> m Bool) -> [a] -> m (Maybe Permutation)
topoSortM parent xs = do
  let nodes     = zip [0..] xs
      parents x = map fst <$> filterM (\(_, y) -> parent y x) nodes
  g <- mapM (mapSndM parents) nodes
  return $ Perm (size xs) <$> topo g
  where

    topo :: Eq node => [(node, [node])] -> Maybe [node]
    topo [] = return []
    topo g  = case xs of
      []    -> fail "cycle detected"
      x : _ -> do
        ys <- topo $ remove x g
        return $ x : ys
      where
        xs = [ x | (x, []) <- g ]
        remove x g = [ (y, filter (/= x) ys) | (y, ys) <- g, x /= y ]

------------------------------------------------------------------------
-- * Drop (apply) and undrop (abstract)
------------------------------------------------------------------------

-- | Delayed dropping which allows undropping.
data Drop a = Drop
  { dropN    :: Int  -- ^ Non-negative number of things to drop.
  , dropFrom :: a    -- ^ Where to drop from.
  }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- | Things that support delayed dropping.
class DoDrop a where

  doDrop :: Drop a -> a              -- ^ Perform the dropping.

  dropMore :: Int -> Drop a -> Drop a  -- ^ Drop more.
  dropMore n (Drop m xs) = Drop (m + n) xs

  unDrop :: Int -> Drop a -> Drop a  -- ^ Pick up dropped stuff.
  unDrop n (Drop m xs)
    | n <= m    = Drop (m - n) xs
    | otherwise = __IMPOSSIBLE__

instance DoDrop [a] where
  doDrop   (Drop m xs) = List.drop m xs

instance DoDrop Permutation where
  doDrop (Drop k (Perm n xs)) =
    Perm (n + m) $ [0..m-1] ++ map (+ m) (List.drop k xs)
    where m = -k
  unDrop m = dropMore (-m) -- allow picking up more than dropped
