module Issue802b where

data I : Set where
  i : I

f : I → I
f i = i

mutual

  data P : I → Set where
    p : (x : I) → Q x x → P (f x)

  Q : I → I → Set
  Q i = P

g : (x y : I) → Q x y → P y
g i _ q = q

data R : (x : I) → P x → Set where
  r : (x : I) (q : Q x x) → R _ (g x _ q) → R (f x) (p x q)
