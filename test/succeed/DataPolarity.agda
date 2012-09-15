-- 2012-02-13 Andreas: testing correct polarity of data types
-- sized types are the only source of subtyping, I think...
{-# OPTIONS -v tc.polarity.set:10 #-}

{-# OPTIONS --sized-types #-}
module DataPolarity where

open import Common.Size

data Nat : {size : Size} -> Set where
  zero : {size : Size} -> Nat {↑ size}
  suc  : {size : Size} -> Nat {size} -> Nat {↑ size}

data Pair (A : Set) : Set where
  _,_ : A -> A -> Pair A

split : {i : Size} → Nat {i} → Pair (Nat {i})
split zero = zero , zero
split (suc n) with split n
... | (l , r) = suc r , l
-- this should work, due to the monotonicity of Pair
-- without subtyping, Agda would complain about i != ↑ i

MyPair : Nat → Set → Set
MyPair zero A = Pair A
MyPair (suc n) A = MyPair n A
-- polarity should be preserved by functions

mysplit : {i : Size} → (n : Nat {i}) → MyPair (suc zero) (Nat {i})
mysplit zero = zero , zero
mysplit (suc n) with mysplit n
... | (l , r) = suc r , l
