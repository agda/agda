------------------------------------------------------------------------
-- Code for converting Vec₁ n A → B to and from n-ary functions
------------------------------------------------------------------------

-- I want universe polymorphism.

module Data.Vec.N-ary1 where

open import Data.Nat
open import Data.Vec1
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- N-ary functions

N-ary : ℕ → Set₁ → Set₁ → Set₁
N-ary zero    A B = B
N-ary (suc n) A B = A → N-ary n A B

------------------------------------------------------------------------
-- Conversion

curryⁿ : ∀ {n A B} → (Vec₁ A n → B) → N-ary n A B
curryⁿ {zero}  f = f []
curryⁿ {suc n} f = λ x → curryⁿ (λ xs → f (x ∷ xs))

_$ⁿ_ : ∀ {n A B} → N-ary n A B → (Vec₁ A n → B)
f $ⁿ []       = f
f $ⁿ (x ∷ xs) = f x $ⁿ xs

------------------------------------------------------------------------
-- N-ary function equality

Eq : ∀ {A B} n → (B → B → Set₁) → (f g : N-ary n A B) → Set₁
Eq zero    _∼_ f g = f ∼ g
Eq (suc n) _∼_ f g = ∀ x → Eq n _∼_ (f x) (g x)

------------------------------------------------------------------------
-- Some lemmas

-- The two functions are inverses.

left-inverse : ∀ {n A B} (f : Vec₁ A n → B) →
               ∀ xs → curryⁿ f $ⁿ xs ≡ f xs
left-inverse f []       = refl
left-inverse f (x ∷ xs) = left-inverse (λ xs → f (x ∷ xs)) xs

data Lift {A : Set₁} (R : A → A → Set) x y : Set₁ where
  lift : R x y → Lift R x y

right-inverse : ∀ {A B} n (f : N-ary n A B) →
                Eq n (Lift _≡_) (curryⁿ (_$ⁿ_ {n} f)) f
right-inverse zero    f = lift refl
right-inverse (suc n) f = λ x → right-inverse n (f x)

-- Conversion preserves equality.

curryⁿ-cong : ∀ {n A B _∼_} (f g : Vec₁ A n → B) →
              (∀ xs → f xs ∼ g xs) →
              Eq n _∼_ (curryⁿ f) (curryⁿ g)
curryⁿ-cong {zero}  f g hyp = hyp []
curryⁿ-cong {suc n} f g hyp = λ x →
  curryⁿ-cong (λ xs → f (x ∷ xs)) (λ xs → g (x ∷ xs))
              (λ xs → hyp (x ∷ xs))

curryⁿ-cong⁻¹ : ∀ {n A B _∼_} (f g : Vec₁ A n → B) →
                Eq n _∼_ (curryⁿ f) (curryⁿ g) →
                ∀ xs → f xs ∼ g xs
curryⁿ-cong⁻¹ f g hyp []       = hyp
curryⁿ-cong⁻¹ f g hyp (x ∷ xs) =
  curryⁿ-cong⁻¹ (λ xs → f (x ∷ xs)) (λ xs → g (x ∷ xs)) (hyp x) xs

appⁿ-cong : ∀ {n A B _∼_} (f g : N-ary n A B) →
            Eq n _∼_ f g →
            (xs : Vec₁ A n) → (f $ⁿ xs) ∼ (g $ⁿ xs)
appⁿ-cong f g hyp []       = hyp
appⁿ-cong f g hyp (x ∷ xs) = appⁿ-cong (f x) (g x) (hyp x) xs

appⁿ-cong⁻¹ : ∀ {n A B _∼_} (f g : N-ary n A B) →
              ((xs : Vec₁ A n) → (f $ⁿ xs) ∼ (g $ⁿ xs)) →
              Eq n _∼_ f g
appⁿ-cong⁻¹ {zero}  f g hyp = hyp []
appⁿ-cong⁻¹ {suc n} f g hyp = λ x →
  appⁿ-cong⁻¹ (f x) (g x) (λ xs → hyp (x ∷ xs))
