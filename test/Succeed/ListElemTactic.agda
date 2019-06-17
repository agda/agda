
module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

variable
  A B : Set
  x y : A
  xs  : List A

infix 3 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  zero : x ∈ x ∷ xs
  suc  : x ∈ xs → x ∈ y ∷ xs

pattern vArg x = arg (arg-info visible relevant) x

search : Nat → Term → Term → TC ⊤
search zero i hole = typeError (strErr "Not found" ∷ [])
search (suc n) i hole = do
  catchTC (noConstraints (unify hole i))
          (search n (con (quote _∈_.suc) (vArg i ∷ [])) hole)

findElem : Nat → Term → TC ⊤
findElem depth hole = search depth (con (quote _∈_.zero) []) hole

index : (x : A) (xs : List A) {@(tactic findElem 10) i : x ∈ xs} → Nat
index x xs {zero}  = zero
index x xs {suc i} = suc (index x _ {i})

test₁ : index 3 (1 ∷ 2 ∷ 3 ∷ []) ≡ 2
test₁ = refl

test₂ : index x (y ∷ x ∷ x ∷ []) ≡ 1
test₂ = refl
