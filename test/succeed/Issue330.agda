-- Adding forcing to functions (f in this case) leaves
-- an unsolved meta of type I (for the argument to f).
module Issue330 where

postulate
 I : Set
 i : I

data D (n : I) : Set where
 d : D n

f : ∀ n → D n → D n
f n d = d

data P : D i → Set where
 c : ∀ v → P (f i v)

p : P d
p = c _
