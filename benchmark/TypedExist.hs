{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
module TypedExist (fromList, toList) where
{- 3rd Version, 2nd typed version -}
{- note that the type variable b is never used anywhere, only passed on. -}


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

delete :: Ord a => a -> Tree a -> Tree a
delete x (ENC t) =
    case delB x t of
        R p -> ENC (B p)
        C(R(a,x,b)) -> ENC(B(C a,x,C b))
        C(C q) -> ENC q

delB :: Ord a => a -> Black a b -> RR a [b]
delB x E = C(C E)
delB x (B(a,y,b))
    | x<y = delfromL a
    | x>y = delfromR b
    | otherwise = appendR a b
      where delfromL(R t) = R(delT x t,y,b)
            delfromL(C E) = R(C E,y,b)
            delfromL(C t) = balL (delB x t) y b
            delfromR(R t) = R(a,y,delT x t)
            delfromR(C E) = R(a,y,C E)
            delfromR(C t) = balR a y (delB x t)

delT :: Ord a => a -> Tr Black a b -> Red Black a b
delT x t@(a,y,b)
    | x<y = delfromL a
    | x>y = delfromR b
    | otherwise = append a b
      where delfromL (B _) = balLeB (delB x a) y b
            delfromL _ = R t
            delfromR (B _) = balRiB a y (delB x b)
            delfromR _ = R t


--balLeB :: RR a [b] -> a -> Black a b -> Red Black a b
balLeB bl x (B y) = balance bl x (R y)

--balRiB :: Black a b -> a -> RR a [b] -> Red Black a b
balRiB (B y) x t = balance (R y) x t

--balL :: RR a [b] -> a -> Red Black a b -> RR a b
balL (R a) y c = R(C(B a),y,c)
balL (C t) x (R(B(a,y,b),z,c)) = R(C(B(t,x,a)),y,balLeB (C b) z c)
balL b x (C t) = C (balLeB b x t)

--balR :: Red Black a b -> a -> RR a [b] -> RR a b
balR a x (R b) = R(a,x,C(B b))
balR (R(a,x,B(b,y,c))) z (C d) = R(balRiB a x (C b),y,C(B(c,z,d)))
balR (C t) x b = C (balRiB t x b)

balance :: RR a [b] -> a -> RR a [b] -> Red Black a b
balance (R a) y (R b) = R(B a,y,B b)
balance (C a) x b = balanceR a x b
balance a x (C b) = balanceL a x b

append :: Black a b -> Black a b -> Red Black a b
append (B(a,x,b)) (B(c,y,d)) = threeformB a x (appendR b c) y d
append _ _ = C E

threeformB :: Red Black a [b] -> a -> RR a [b] -> a -> Red Black a [b] -> Red Black a b
threeformB a x (R(b,y,c)) z d = R(B(a,x,b),y,B(c,z,d))
threeformB a x (C b) y c = balLeB (C a) x (B(b,y,c))

appendR :: Red Black a b -> Red Black a b -> RR a b
appendR (C x) (C y) = C(append x y)
appendR (C t) (R(a,x,b)) = R(append t a,x,C b)
appendR (R(a,x,b)) (C t) = R(C a,x,append b t)
appendR (R(a,x,b))(R(c,y,d)) = threeformR a x (append b c) y d

threeformR:: Black a b -> a -> Red Black a b -> a -> Black a b -> RR a b
threeformR a x (R(b,y,c)) z d = R(R(a,x,b),y,R(c,z,d))
threeformR a x (C b) y c = R(R(a,x,b),y,C c)

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

