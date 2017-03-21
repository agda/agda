{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Typed (fromList, toList) where

import qualified Data.Foldable as F

{- Version 2, 1st typed version -}
data Unit a = E deriving Show
type Tr t a = (t a,a,t a)
data Red t a = C (t a) | R (Tr t a)

{- explicit Show instance as we work with 3rd order type constructors -}
instance (Show (t a), Show a) => Show (Red t a)
 where showsPrec _ (C t) = shows t
       showsPrec _ (R(a,b,c)) =
         ("R("++) . shows a . (","++) . shows b . (","++) . shows c . (")"++)

data AddLayer t a = B(Tr(Red t) a) deriving Show

data RB t a = Base (t a) | Next (RB (AddLayer t) a)

{- this Show instance is not Haskell98, but hugs -98 accepts it -}
instance (Show (t a),Show a) => Show (RB t a)
    where
    show (Base t) = show t
    show (Next t) = show t

type Tree a = RB Unit a
empty :: Tree a
empty = Base E

type RR t a = Red (Red t) a
type RL t a = Red (AddLayer t) a

member :: Ord a => a -> Tree a -> Bool
member x t = rbmember x t (\ _ -> False)

rbmember :: Ord a => a -> RB t a -> (t a->Bool) -> Bool
rbmember x (Base t) m = m t
rbmember x (Next u) m = rbmember x u (bmem x m)

bmem :: Ord a => a -> (t a->Bool) -> AddLayer t a -> Bool
bmem x m (B(l,y,r))
 | x<y = rmem x m l
 | x>y = rmem x m r
 | otherwise = True

rmem :: Ord a => a -> (t a->Bool) -> Red t a->Bool
rmem x m (C t) = m t
rmem x m (R(l,y,r))
 | x<y = m l
 | x>y = m r
 | otherwise = True

insert :: Ord a => a -> Tree a -> Tree a
insert = rbinsert

class Insertion t where ins :: Ord a => a -> t a -> Red t a
instance Insertion Unit where ins x E = R(E,x,E)

rbinsert :: (Ord a,Insertion t) => a -> RB t a -> RB t a
rbinsert x (Next t) = Next (rbinsert x t)
rbinsert x (Base t) = blacken(ins x t)

blacken :: Red t a -> RB t a
blacken (C u) = Base u
blacken (R(a,x,b)) = Next(Base(B(C a,x,C b)))

balanceL :: RR t a -> a -> Red t a -> RL t a
balanceL (R(R(a,x,b),y,c)) z d = R(B(C a,x,C b),y,B(c,z,d))
balanceL (R(a,x,R(b,y,c))) z d = R(B(a,x,C b),y,B(C c,z,d))
balanceL (R(C a,x,C b)) z d = C(B(R(a,x,b),z,d))
balanceL (C a) x b = C(B(a,x,b))

balanceR :: Red t a -> a -> RR t a -> RL t a
balanceR a x (R(R(b,y,c),z,d)) = R(B(a,x,C b),y,B(C c,z,d))
balanceR a x (R(b,y,R(c,z,d))) = R(B(a,x,b),y,B(C c,z,C d))
balanceR a x (R(C b,y,C c)) = C(B(a,x,R(b,y,c)))
balanceR a x (C b) = C(B(a,x,b))

instance Insertion t => Insertion (AddLayer t) where
  ins x t@(B(l,y,r))
    | x<y = balance(ins x l) y (C r)
    | x>y = balance(C l) y (ins x r)
    | otherwise = C t
instance Insertion t => Insertion (Red t) where
  ins x (C t) = C(ins x t)
  ins x t@(R(a,y,b))
    | x<y = R(ins x a,y,C b)
    | x>y = R(C a,y,ins x b)
    | otherwise = C t

balance :: RR t a -> a -> RR t a -> RL t a
balance (R a) y (R b) = R(B a,y,B b)
balance (C a) x b = balanceR a x b
balance a x (C b) = balanceL a x b

class Append t where app :: t a -> t a -> Red t a

instance Append Unit where app _ _ = C E

instance Append t => Append (AddLayer t) where
    app (B(a,x,b)) (B(c,y,d)) = threeformB a x (appRed b c) y d

threeformB :: Red t a -> a -> RR t a -> a -> Red t a -> RL t a
threeformB a x (R(b,y,c)) z d = R(B(a,x,b),y,B(c,z,d))
threeformB a x (C b) y c = balleftB (C a) x (B(b,y,c))

appRed :: Append t => Red t a -> Red t a -> RR t a
appRed (C x) (C y) = C(app x y)
appRed (C t) (R(a,x,b)) = R(app t a,x,C b)
appRed (R(a,x,b)) (C t) = R(C a,x,app b t)
appRed (R(a,x,b))(R(c,y,d)) = threeformR a x (app b c) y d

threeformR:: t a -> a -> Red t a -> a -> t a -> RR t a
threeformR a x (R(b,y,c)) z d = R(R(a,x,b),y,R(c,z,d))
threeformR a x (C b) y c = R(R(a,x,b),y,C c)

balleft :: RR t a -> a -> RL t a -> RR (AddLayer t) a
balleft (R a) y c = R(C(B a),y,c)
balleft (C t) x (R(B(a,y,b),z,c)) = R(C(B(t,x,a)),y,balleftB (C b) z c)
balleft b x (C t) = C (balleftB b x t)

balleftB :: RR t a -> a -> AddLayer t a -> RL t a
balleftB bl x (B y) = balance bl x (R y)

balright :: RL t a -> a -> RR t a -> RR (AddLayer t) a
balright a x (R b) = R(a,x,C(B b))
balright (R(a,x,B(b,y,c))) z (C d) = R(balrightB a x (C b),y,C(B(c,z,d)))
balright (C t) x b = C (balrightB t x b)

balrightB :: AddLayer t a -> a -> RR t a -> RL t a
balrightB (B y) x t = balance (R y) x t

class Append t => DelRed t where
  delTup :: Ord a => a -> Tr t a -> Red t a
  delLeft :: Ord a => a -> t a -> a -> Red t a -> RR t a
  delRight :: Ord a => a -> Red t a -> a -> t a -> RR t a

class Append t => Del t where
  del :: Ord a => a -> AddLayer t a -> RR t a

class (DelRed t, Del t) => Deletion t

instance DelRed Unit where
  delTup z t@(_,x,_) = if x==z then C E else R t
  delLeft x _ y b = R(C E,y,b)
  delRight x a y _ = R(a,y,C E)

instance Deletion t => DelRed (AddLayer t) where
  delTup z (a,x,b)
    | z<x = balleftB (del z a) x b
    | z>x = balrightB a x (del z b)
    | otherwise = app a b
  delLeft x a y b = balleft (del x a) y b
  delRight x a y b = balright a y (del x b)

instance (Append t, DelRed t) => Del t where
  del z (B(a,x,b))
    | z<x = delformLeft a
    | z>x = delformRight b
    | otherwise = appRed a b
    where delformLeft(C t) = delLeft z t x b
          delformLeft(R t) = R(delTup z t,x,b)
          delformRight(C t) = delRight z a x t
          delformRight(R t) = R(a,x,delTup z t)

instance Deletion t => Deletion (AddLayer t)
instance Deletion Unit

rbdelete :: (Ord a,Deletion t) => a -> RB (AddLayer t) a -> RB t a
rbdelete x (Next t) = Next (rbdelete x t)
rbdelete x (Base t) = blacken2 (del x t)

blacken2 :: RR t a -> RB t a
blacken2 (C(C t)) = Base t
blacken2 (C(R(a,x,b))) = Next(Base(B(C a,x,C b)))
blacken2 (R p) = Next(Base(B p))

delete :: Ord a => a -> Tree a -> Tree a
delete x (Next u) = rbdelete x u
delete x _ = empty

fromList :: Ord a => [a] -> Tree a
fromList = foldr insert empty

instance Foldable Unit where
  foldr _ x E = x

instance Foldable (RB Unit) where
  foldr f x t = case t of
    (Base E) -> x
    (Next t') -> foldr f x t'

instance (Foldable a) => Foldable (RB (AddLayer a)) where
  foldr f x t = case t of
    (Base (B (lhs, a, rhs))) -> r
      where
        l = foldr f (f a x) lhs
        r = foldr f l rhs
    (Next t') -> foldr f x t'

instance (Foldable a) => Foldable (AddLayer a) where
  foldr f x (B (lhs, a, rhs)) = r
    where
      l = foldr f (f a x) lhs
      r = foldr f l rhs

instance Foldable a => Foldable (Red a) where
  foldr f x t = case t of
    C t' -> foldr f x t'
    R (lhs, a, rhs) -> r
      where
        l = foldr f (f a x) lhs
        r = foldr f l rhs

toList :: Tree a -> [a]
toList = F.toList
