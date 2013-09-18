-- 2012-02-13 Andreas: testing correct polarity of data types
-- sized types are the only source of subtyping, I think...
-- {-# OPTIONS -v tc.polarity.set:10 #-}
-- {-# OPTIONS -v tc.size.solve:20 #-}

{-# OPTIONS --show-implicit #-}
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

-- it should also work in modules

module M (s : Set1) where

  data P (A : Set) : Set where
    _,_ : A -> A -> P A

  sp : {i : Size} → (n : Nat {i}) → P (Nat {i})
  sp zero = zero , zero
  sp (suc n) with sp n
  ... | (l , r) = suc r , l

-- open import Common.Prelude

postulate A : Set

data Color : Set where
  red   : Color
  black : Color

data Bounds : Set where
  leftOf : Bounds → Bounds
  rightOf : Bounds → Bounds

-- works not:
data Tree' (β : Bounds) : {i : Size} -> Color → (Nat {∞}) → Set where
  lf : ∀ {i} → Tree' β {↑ i} black zero
  nr : ∀ {i n}(a : A) -- →  .(a is β)
     → Tree' (leftOf  β) {i} black n
     → Tree' (rightOf β) {i} black n
     → Tree' β {↑ i} red n
  nb : ∀ {i c n}(a : A) -- → .(a is β)
     → Tree' (leftOf β) {i} c n
     → Tree' (rightOf β) {i} black n
     → Tree' β {↑ i} black (suc n)

-- works:
data Tr (A : Set) : {i : Size} -> Color → Set where
  lf : ∀ {i} → Tr A {↑ i} black
  nr : ∀ {i}(a : A)
     → Tr A {i} black → Tr A {i} black
     → Tr A {↑ i} red
  nb : ∀ {i c}(a : A)
     → Tr A {i} c → Tr A {i} black
     → Tr A {↑ i} black

