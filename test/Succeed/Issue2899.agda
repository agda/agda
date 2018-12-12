{-# OPTIONS -WUnknownFixityInMixfixDecl #-}

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

_+_ : Nat → Nat → Nat
zero + n = n
(suc m) + n = suc (m + n)

private
  _*_ : Nat → Nat → Nat
  zero    * n = zero
  (suc m) * n = n + (m * n)

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

foldr : {A B : Set} → (A → B → B) → B → List A → B
foldr _<>_ n []       = n
foldr _<>_ n (x ∷ xs) = x <> (foldr _<>_ n xs)

sumOfPowers : Nat → List Nat → Nat
sumOfPowers x = foldr (λ p → (x ^ p) +_) zero where

  _^_ : Nat → Nat → Nat
  m ^ zero  = suc zero
  m ^ suc n = m * (m ^ n)
