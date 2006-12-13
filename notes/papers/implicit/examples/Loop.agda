
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

delta = lam _ _ (\x -> app _ _ x x)

