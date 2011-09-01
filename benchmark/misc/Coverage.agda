module Coverage where

infixr 40 _::_
data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

data D : Set where
  c1 : D -> D
  c2 : D
  c3 : D -> D -> D -> D
  c4 : D -> D -> D

f : D -> D -> D -> D -> List D
f (c3 a (c1 b) (c1 c2)) (c1 (c1 c)) d (c1 (c1 (c1 e))) = a :: b :: c :: d :: e :: []
f (c3 (c4 c2 a) (c1 b) (c1 c)) d (c1 (c1 e)) (c1 (c1 (c1 f))) = a :: b :: c :: d :: e :: f :: []
f a b (c1 c) (c3 d (c1 e) (c1 f)) = a :: b :: c :: d :: e :: f :: []
f (c3 (c4 a c2) b (c1 c)) (c1 d) (c1 (c1 (c1 e))) (c1 (c1 (c1 f))) = a :: b :: c :: d :: e :: f :: []
-- f (c3 a (c1 b) c) (c1 (c1 (c1 d))) (c1 (c1 (c1 e))) f = a :: b :: c :: d :: e :: f :: []
-- f a b (c1 (c1 c)) (c1 (c1 (c1 c2))) = a :: b :: c :: []
f a b c d = a :: b :: c :: d :: []

