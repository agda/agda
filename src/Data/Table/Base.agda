------------------------------------------------------------------------
-- The Agda standard library
--
-- Tables, basic types and operations
------------------------------------------------------------------------

module Data.Table.Base where

open import Data.Fin
open import Data.List as List using (List)
open import Data.Nat
open import Function using (_∘_)

record Table {a} (A : Set a) n : Set a where
  constructor tabulate
  field
    lookup : Fin n → A

open Table public

map : ∀ {n a b} {A : Set a} {B : Set b} → (A → B) → Table A n → Table B n
map f t = tabulate (f ∘ lookup t)


-- A contravariant map over the indices

rearrange : ∀ {a} {A : Set a} {m n} → (Fin m → Fin n) → Table A n → Table A m
rearrange f t = tabulate (lookup t ∘ f)

head : ∀ {n a} {A : Set a} → Table A (ℕ.suc n) → A
head t = lookup t zero

tail : ∀ {n a} {A : Set a} → Table A (ℕ.suc n) → Table A n
tail t = tabulate (lookup t ∘ suc)

toList : ∀ {n a} {A : Set a} → Table A n → List A
toList = List.tabulate ∘ lookup

fromList : ∀ {a} {A : Set a} (xs : List A) → Table A (List.length xs)
fromList = tabulate ∘ List.lookup

foldr : ∀ {a b} {A : Set a} {B : Set b} {n} → (A → B → B) → B → Table A n → B
foldr {n = zero}  f z t = z
foldr {n = suc n} f z t = f (lookup t zero) (foldr f z (tail t))

foldl : ∀ {a b} {A : Set a} {B : Set b} {n} → (B → A → B) → B → Table A n → B
foldl {n = zero}  f z t = z
foldl {n = suc n} f z t = foldl f (f z (lookup t zero)) (tail t)

replicate : ∀ {n a} {A : Set a} → A → Table A n
replicate x = tabulate (λ _ → x)

_⊛_ : ∀ {n a b} {A : Set a} {B : Set b} → Table (A → B) n → Table A n → Table B n
fs ⊛ xs = tabulate λ i → lookup fs i (lookup xs i)
