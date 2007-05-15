{-# OPTIONS -fglasgow-exts #-}

module Utils.Permutation where

import Data.List
import Utils.Size

-- | @permute [2,3,1] [x,y,z] = [y,z,x]@
data Permutation = Perm Int [Int]
  deriving (Show)

instance Sized Permutation where
  size (Perm _ xs) = size xs

permute :: Permutation -> [a] -> [a]
permute (Perm _ is) xs = map (xs !!) is

idP :: Int -> Permutation
idP n = Perm n [0..n - 1]

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
invertP (Perm n xs) = Perm (size xs) $ map inv [0..n - 1]
  where
    inv x = case findIndex (x ==) xs of
	      Just y  -> y
	      Nothing -> error $ "invertP: non-surjective permutation " ++ show xs

reverseP :: Permutation -> Permutation
reverseP (Perm n xs) = Perm n $ map ((n - 1) -) $ reverse xs

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

