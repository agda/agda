-- Andreas, 2015-07-20, record patterns

open import Common.Product
open import Common.Prelude
open import Common.Equality

swap : {A B : Set} (p : A × B) → B × A
swap record{ proj₁ = a; proj₂ = b } = record{ proj₁ = b; proj₂ = a }

fst : {A : Set}{B : A → Set} (p : Σ A B) → A
fst record{ proj₁ = a } = a

snd : {A : Set}{B : A → Set} (p : Σ A B) → B (fst p)
snd record{ proj₂ = b } = b

module _ (A : Set) (B : A → Set) (C : (a : A) → B a → Set) where

  Tr = Σ A (λ a → Σ (B a) (C a))

  fst3 : Tr → A
  fst3 record{ proj₁ = a } = a

  snd3 : (t : Tr) → B (fst3 t)
  snd3 record{ proj₂ = record { proj₁ = b }} = b

  thd3 : (t : Tr) → C (fst3 t) (snd3 t)
  thd3 record{ proj₂ = record { proj₂ = c }} = c

  thd32 : (t u : Tr) → C (fst3 t) (snd3 t)
  thd32 record{ proj₂ = record { proj₂ = c }}
        record{ proj₂ = record { proj₂ = _ }} = c

postulate A : Set

record R : Set where
  field f : A

T : Bool → Set
T true  = R
T false = A

-- Postponed record pattern
test : ∀{b} → T b → b ≡ true → A
test record{f = a} refl = a
