
module Loop where

{-
data _=>_ (A, B : Set) : Set where
  lam : (A -> B) -> A => B

app : {A, B : Set} -> (A => B) -> A -> B
app (lam f) = f

delta = lam (\x -> app x x)

loop = app delta delta
-}

lam : (A, B : Set) -> (A -> B) -> A -> B
lam A B f = f

app : (A, B : Set) -> (A -> B) -> A -> B
app A B f = f

postulate Nat : Set
	  zero : Nat

wrap : (F : Nat -> Set) -> F zero -> F zero
wrap F x = x

delta : (Nat -> Nat) -> Nat
delta = \x -> x (wrap _ x)

loop : Nat
loop = delta (wrap _ delta)

-- delta : _ -> _
-- delta = \x -> app _ _ x x -- lam _ _ (\x -> app _ _ x x)
-- 
-- loop = app _ _ delta (wrap _ delta)
