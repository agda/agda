module Untyped (Tree, fromList, fromList', toList) where

import qualified Data.Foldable as F
import Data.List (foldl')

{- Version 1, 'untyped' -}
data Color = R | B deriving Show
data RB a = E | T { color :: Color , left :: RB a , rootLabel :: a , right :: RB a } deriving Show

{- Insertion and membership test as by Okasaki -}
insert :: Ord a => a -> RB a -> RB a
insert x s =
  T B a z b
  where
    T _ a z b = ins s
    ins E = T R E x E
    ins s@(T B a y b)
      | x<y = balance (ins a) y b
      | x>y = balance a y (ins b)
      | otherwise = s
    ins s@(T R a y b)
      | x<y = T R (ins a) y b
      | x>y = T R a y (ins b)
      | otherwise = s

{- balance: first equation is new,
   to make it work with a weaker invariant -}
balance :: RB a -> a -> RB a -> RB a
balance (T R a x b) y (T R c z d) = T R (T B a x b) y (T B c z d)
balance (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance a x b = T B a x b

type Tree a = RB a

empty :: Tree a
empty = E

fromList' :: Ord a => [a] -> Tree a
fromList' = foldl' (flip insert) empty

fromList :: Ord a => [a] -> Tree a
fromList = foldr insert empty

instance Foldable RB where
  foldr f x t = case t of
    E{} -> x
    T{} -> r
      where
        a = rootLabel t
        l = foldr f (f a x) (left t)
        r = foldr f l (right t)

toList :: Tree a -> [a]
toList = F.toList
