module RecursiveInstanceSearch where

open import Common.Prelude
open import Common.Product

_&&_ : Bool → Bool → Bool
true && b = b
false && _ = false

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A → Maybe A

record Eq (A : Set) : Set where
  constructor eq
  field
    _==_ : A → A → Bool
open Eq {{...}} public

instance
  eq-Bool : Eq Bool
  eq-Bool = eq aux  where

    aux : Bool → Bool → Bool
    aux true true = true
    aux false false = true
    aux _ _ = false

  eq-Nat : Eq Nat
  eq-Nat = eq aux  where

    aux : Nat → Nat → Bool
    aux zero zero = true
    aux (suc n) (suc m) = aux n m
    aux _ _ = false

  eq-Maybe : {A : Set} → Eq A → Eq (Maybe A)
  eq-Maybe {A} eqA = eq aux  where

    aux : Maybe A → Maybe A → Bool
    aux Nothing Nothing = true
    aux (Just y) (Just z) = (y == z)
    aux _ _ = false

  eq-List : {A : Set} → Eq A → Eq (List A)
  eq-List {A} eqA = eq aux  where

    aux : List A → List A → Bool
    aux [] [] = true
    aux (x ∷ l) (y ∷ l') = (x == y) && (aux l l')
    aux _ _ = false

  eq-× : {A B : Set} → Eq A → Eq B → Eq (A × B)
  eq-× {A} {B} eqA eqB = eq (λ x y → (proj₁ x == proj₁ y) && (proj₂ x == proj₂ y))

test₂ : Bool
test₂ = (3 == 4)

test₃ : Bool
test₃ = ((Just 9) == Nothing)

test₃' : Bool
test₃' = (Nothing == Just 6)

test₄ : Bool
test₄ = (true ∷ []) == (false ∷ [])

test₅ : Bool
test₅ = (Just ((true ,′ (1 ,′ Just 0)) ∷ []) == Just ((true , (1 , Just 0)) ∷ []))
