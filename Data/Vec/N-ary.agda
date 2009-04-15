------------------------------------------------------------------------
-- Code for converting Vec n A → B to and from n-ary functions
------------------------------------------------------------------------

module Data.Vec.N-ary where

open import Data.Nat
open import Data.Vec
open import Data.Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- N-ary functions

N-ary : ℕ → Set → Set → Set
N-ary zero    A B = B
N-ary (suc n) A B = A → N-ary n A B

------------------------------------------------------------------------
-- Conversion

curryⁿ : ∀ {n A B} → (Vec A n → B) → N-ary n A B
curryⁿ {zero}  f = f []
curryⁿ {suc n} f = λ x → curryⁿ (f ∘ _∷_ x)

_$ⁿ_ : ∀ {n A B} → N-ary n A B → (Vec A n → B)
f $ⁿ []       = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs

------------------------------------------------------------------------
-- N-ary function equality

Eq : ∀ {A B} n → Rel B → (f g : N-ary n A B) → Set
Eq zero    _∼_ f g = f ∼ g
Eq (suc n) _∼_ f g = ∀ x → Eq n _∼_ (f x) (g x)

-- A variant where all the arguments are implicit (hidden).

Eqʰ : ∀ {A B} n → Rel B → (f g : N-ary n A B) → Set
Eqʰ zero    _∼_ f g = f ∼ g
Eqʰ (suc n) _∼_ f g = ∀ {x} → Eqʰ n _∼_ (f x) (g x)

------------------------------------------------------------------------
-- Some lemmas

-- The functions curryⁿ and _$ⁿ_ are inverses.

left-inverse : ∀ {n A B} (f : Vec A n → B) →
               ∀ xs → curryⁿ f $ⁿ xs ≡ f xs
left-inverse f []       = refl
left-inverse f (x ∷ xs) = left-inverse (f ∘ _∷_ x) xs

right-inverse : ∀ {A B} n (f : N-ary n A B) →
                Eq n _≡_ (curryⁿ (_$ⁿ_ {n} f)) f
right-inverse zero    f = refl
right-inverse (suc n) f = λ x → right-inverse n (f x)

-- Conversion preserves equality.

curryⁿ-pres : ∀ {n A B _∼_} (f g : Vec A n → B) →
              (∀ xs → f xs ∼ g xs) →
              Eq n _∼_ (curryⁿ f) (curryⁿ g)
curryⁿ-pres {zero}  f g hyp = hyp []
curryⁿ-pres {suc n} f g hyp = λ x →
  curryⁿ-pres (f ∘ _∷_ x) (g ∘ _∷_ x) (λ xs → hyp (x ∷ xs))

curryⁿ-pres⁻¹ : ∀ {n A B _∼_} (f g : Vec A n → B) →
                Eq n _∼_ (curryⁿ f) (curryⁿ g) →
                ∀ xs → f xs ∼ g xs
curryⁿ-pres⁻¹ f g hyp []       = hyp
curryⁿ-pres⁻¹ f g hyp (x ∷ xs) =
  curryⁿ-pres⁻¹ (f ∘ _∷_ x) (g ∘ _∷_ x) (hyp x) xs

appⁿ-pres : ∀ {n A B _∼_} (f g : N-ary n A B) →
            Eq n _∼_ f g →
            (xs : Vec A n) → (f $ⁿ xs) ∼ (g $ⁿ xs)
appⁿ-pres f g hyp []       = hyp
appⁿ-pres f g hyp (x ∷ xs) = appⁿ-pres (f x) (g x) (hyp x) xs

appⁿ-pres⁻¹ : ∀ {n A B _∼_} (f g : N-ary n A B) →
              ((xs : Vec A n) → (f $ⁿ xs) ∼ (g $ⁿ xs)) →
              Eq n _∼_ f g
appⁿ-pres⁻¹ {zero}  f g hyp = hyp []
appⁿ-pres⁻¹ {suc n} f g hyp = λ x →
  appⁿ-pres⁻¹ (f x) (g x) (λ xs → hyp (x ∷ xs))

-- Eq and Eqʰ are equivalent.

Eq-to-Eqʰ : ∀ {A B} n {_∼_ : Rel B} {f g : N-ary n A B} →
            Eq n _∼_ f g → Eqʰ n _∼_ f g
Eq-to-Eqʰ zero    eq = eq
Eq-to-Eqʰ (suc n) eq = Eq-to-Eqʰ n (eq _)

Eqʰ-to-Eq : ∀ {A B} n {_∼_ : Rel B} {f g : N-ary n A B} →
            Eqʰ n _∼_ f g → Eq n _∼_ f g
Eqʰ-to-Eq zero    eq = eq
Eqʰ-to-Eq (suc n) eq = λ _ → Eqʰ-to-Eq n eq
