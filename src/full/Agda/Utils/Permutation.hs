{-# LANGUAGE DeriveDataTypeable, CPP #-}
module Agda.Utils.Permutation where

import Data.Typeable (Typeable)
import Data.List
import Agda.Utils.Size
import Agda.Utils.Impossible

#include "../undefined.h"

-- | @permute [1,2,0] [x0,x1,x2] = [x1,x2,x0]@
--
--   Agda typing would be:
--   @Perm : {m : Nat}(n : Nat) -> Vec (Fin n) m -> Permutation@
--   @m@ is the 'size' of the permutation.
data Permutation = Perm { permRange :: Int, permPicks :: [Int] }
  deriving (Eq, Typeable)

instance Show Permutation where
  show (Perm n xs) = showx [0..n - 1] ++ " -> " ++ showx xs
    where showx = showList "," (\ i -> "x" ++ show i)
          showList :: String -> (a -> String) -> [a] -> String
          showList sep f [] = ""
          showList sep f [e] = f e
          showList sep f (e:es) = f e ++ sep ++ showList sep f es

instance Sized Permutation where
  size (Perm _ xs) = size xs

-- | @permute [1,2,0] [x0,x1,x2] = [x1,x2,x0]@
--   More precisely, @permute indices list = sublist@, generates @sublist@
--   from @list@ by picking the elements of list as indicated by @indices@.
--   @permute [1,3,0] [x0,x1,x2,x3] = [x1,x3,x0]@
--
--   Agda typing:
--   @permute (Perm {m} n is) : Vec A m -> Vec A n@
permute :: Permutation -> [a] -> [a]
permute (Perm _ is) xs = map (xs !!!) is
  where
    []     !!! _ = __IMPOSSIBLE__
    (x:xs) !!! 0 = x
    (x:xs) !!! n = xs !!! (n - 1)

idP :: Int -> Permutation
idP n = Perm n [0..n - 1]

takeP :: Int -> Permutation -> Permutation
takeP n (Perm m xs) = Perm n $ filter (< n) xs

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

invertP :: Permutation -> Permutation
invertP p@(Perm n xs) = Perm (size xs) $ map inv [0..n - 1]
  where
    inv x = case findIndex (x ==) xs of
	      Just y  -> fromIntegral y
	      Nothing -> error $ "invertP: non-surjective permutation " ++ show p

-- | Turn a possible non-surjective permutation into a surjective permutation.
compactP :: Permutation -> Permutation
compactP (Perm n xs) = Perm m $ map adjust xs
  where
    m            = genericLength xs
    missing      = [0..n - 1] \\ xs
    holesBelow k = genericLength $ filter (< k) missing
    adjust k = k - holesBelow k

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
reverseP :: Permutation -> Permutation
reverseP (Perm n xs) = Perm n $ map ((n - 1) -) $ reverse xs

-- | @expandP i n π@ in the domain of @π@ replace the /i/th element by /n/ elements.
expandP :: Int -> Int -> Permutation -> Permutation
expandP i n (Perm m xs) = Perm (m + n - 1) $ concatMap expand xs
  where
    expand j
      | j == i	  = [i..i + n - 1]
      | j < i	  = [j]
      | otherwise = [j + n - 1]

-- | Stable topologic sort. The first argument decides whether its first
--   argument is an immediate parent to its second argument.
topoSort :: (a -> a -> Bool) -> [a] -> Maybe Permutation
topoSort parent xs = fmap (Perm (size xs)) $ topo g
  where
    nodes     = zip [0..] xs
    g	      = [ (n, parents x) | (n, x) <- nodes ]
    parents x = [ n | (n, y) <- nodes, parent y x ]

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
