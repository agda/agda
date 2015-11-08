
module Issue450 where

open import Common.Level
open import Common.Coinduction

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

data Wrap (A : Set) : Set where
  con : A -> Wrap A

out : forall {A} -> Wrap A -> A
out (con x) = x

out' : forall {A} -> ∞ (Wrap A) -> A
out' y = out (♭ y)

inn : forall {A}  -> A -> ∞ (Wrap A)
inn y = ♯ (con y)

prf : (A : Set)(x : A) → out' (inn x) ≡ x
prf A x = refl

test : forall {A : Set}{x : A} -> out (con x) ≡ x
test = refl

-- these work
test1 : forall {A}{x : A} -> out' (inn x) ≡ x
test1 {A} {x} = test

test2 : forall {A}{x : A} -> out' (inn x) ≡ x
test2 {A} {x} = test {A}

-- but the following ones won't typecheck

test3 : forall {A}{x : A} -> out' (inn x) ≡ x
test3 {A} {x} = test {A} {x}

test4 : forall {A}{x : A} -> out' (inn x) ≡ x
test4 {A} {x} = refl
