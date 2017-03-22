{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
module TypedExist (Tree, fromList, fromList', toList) where
{- 3rd Version, 2nd typed version -}
{- note that the type variable b is never used anywhere, only passed on. -}

import Data.List (foldl')

type Tr t a b = (t a b, a, t a b)
data Red t a b = C (t a b) | R (Tr t a b)
data Black a b = E | B (Tr (Red Black) a [b])

instance Show a => Show (Black a b) where
    showsPrec _ E = ('E':)
    showsPrec _ (B(a,x,b)) = ("B("++) . showRed a . (","++) . shows x .
                             (","++) . showRed b . (")"++)

showRed :: (Show (t1 a t), Show a) => Red t1 a t -> ShowS
showRed (C x) = shows x
showRed (R(a,x,b)) = ("R("++) . shows a . (","++) . shows x . (","++) .
                     shows b . (")"++)

type RR a b = Red (Red Black) a b

inc :: Black a b -> Black a [b]
inc = tickB

{- tickB is the identity,
   but it allows us to replace that bogus type variable -}

tickB :: Black a b -> Black a c
tickB E = E
tickB (B(a,x,b)) = B(tickR a,x,tickR b)

tickR :: Red Black a b -> Red Black a c
tickR (C t) = C(tickB t)
tickR (R(a,x,b)) = R(tickB a,x,tickB b)

data Tree a = forall b . ENC (Black a b)

instance Show a => Show (Tree a)
    where show (ENC t) = show t

empty :: Tree a
empty = ENC E

insert :: Ord a => a -> Tree a -> Tree a
insert x (ENC t) = ENC(blacken (insB x t))

blacken :: Red Black a b -> Black a b
blacken (C u) = u
blacken (R(a,x,b)) = B(C(inc a),x,C(inc b))

insB :: Ord a => a -> Black a b -> Red Black a b
insB x E = R(E,x,E)
insB x t@(B(a,y,b))
    | x<y = balanceL (insR x a) y b
    | x>y = balanceR a y (insR x b)
    | otherwise = C t

insR :: Ord a => a -> Red Black a b -> RR a b
insR x (C t) = C(insB x t)
insR x t@(R(a,y,b))
    | x<y = R(insB x a,y,C b)
    | x>y = R(C a,y,insB x b)
    | otherwise = C t

--balanceL :: RR a [b] -> a -> Red Black a [b] -> Red Black a b
balanceL (R(R(a,x,b),y,c)) z d = R(B(C a,x,C b),y,B(c,z,d))
balanceL (R(a,x,R(b,y,c))) z d = R(B(a,x,C b),y,B(C c,z,d))
balanceL (R(C a,x,C b)) z d = C(B(R(a,x,b),z,d))
balanceL (C a) x b = C(B(a,x,b))

--balanceR :: Red Black a [b] -> a -> RR a [b] -> Red Black a b
balanceR a x (R(R(b,y,c),z,d)) = R(B(a,x,C b),y,B(C c,z,d))
balanceR a x (R(b,y,R(c,z,d))) = R(B(a,x,b),y,B(C c,z,C d))
balanceR a x (R(C b,y,C c)) = C(B(a,x,R(b,y,c)))
balanceR a x (C b) = C(B(a,x,b))


fromList' :: Ord a => [a] -> Tree a
fromList' = foldl' (flip insert) empty

fromList :: Ord a => [a] -> Tree a
fromList = foldr insert empty

toList :: Tree a -> [a]
toList (ENC tr) = toListBlack tr

toListRed :: Red Black a [b] -> [a]
toListRed (C rd) = toListBlack rd
toListRed (R (l, a, r)) = toListBlack l ++ [a] ++ toListBlack r

toListBlack :: Black a b -> [a]
toListBlack E  = []
toListBlack (B (l, a, r)) = toListRed l ++ [a] ++ toListRed r

