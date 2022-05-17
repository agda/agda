{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Coinduction
open import Agda.Builtin.IO
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Unit

private
  variable
    A : Set

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}

record Stream₁ (A : Set) : Set where
  coinductive
  constructor _∷_
  field
    head : A
    tail : Stream₁ A

open Stream₁

repeat₁ : A → Stream₁ A
repeat₁ x .head = x
repeat₁ x .tail = repeat₁ x

take₁ : Nat → Stream₁ A → List A
take₁ zero    xs = []
take₁ (suc n) xs = xs .head ∷ take₁ n (xs .tail)

data List′ (A : Set) : Set where
  []  : List′ A
  _∷_ : A → List′ A → List′ A

to-list : List′ A → List A
to-list []       = []
to-list (x ∷ xs) = x ∷ to-list xs

data Stream₂ (A : Set) : Set where
  _∷_ : A → ∞ (Stream₂ A) → Stream₂ A

repeat₂ : A → Stream₂ A
repeat₂ x = x ∷ ♯ repeat₂ x

take₂ : Nat → Stream₂ A → List′ A
take₂ zero    _        = []
take₂ (suc n) (x ∷ xs) = x ∷ take₂ n (♭ xs)

_++_ : List A → List′ A → List A
[]       ++ ys = to-list ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

main : IO ⊤
main =
  putStrLn
    (primStringFromList
       (take₁ 3 (repeat₁ '(') ++ take₂ 3 (repeat₂ ')')))
