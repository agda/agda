-- Andreas, 2016-06-26 issue #2066, reported by Mietek Bak
-- already fixed on stable-2.5

open import Data.Nat using (ℕ ; zero ; suc ; _≟_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (yes ; no)

data Tm : Set where
  var : ℕ → Tm
  lam : ℕ → Tm → Tm
  app : Tm → Tm → Tm

data _∥_ (x : ℕ) : Tm → Set where
  var∥  : ∀ {y} → y ≢ x → x ∥ var y
  ≡lam∥ : ∀ {t} → x ∥ lam x t
  ≢lam∥ : ∀ {y t} → x ∥ t → x ∥ lam y t
  app∥  : ∀ {t u} → x ∥ t → x ∥ u → x ∥ app t u

_∥?_ : Decidable _∥_
x ∥? var y with y ≟ x
x ∥? var .x | yes refl = no (λ { (var∥ x≢x) → x≢x refl })
x ∥? var y  | no  y≢x  = yes (var∥ y≢x)
x ∥? lam y t with y ≟ x | x ∥? t
x ∥? lam .x t | yes refl | _       = yes ≡lam∥
x ∥? lam y  t | no  y≢x  | yes x∥t = yes (≢lam∥ x∥t)
x ∥? lam y  t | no  y≢x  | no  x∦t = no (λ { ≡lam∥ → {!!} ; (≢lam∥ p) → {!!} })
x ∥? app t u with x ∥? t | x ∥? u
x ∥? app t u | yes x∥t | yes x∥u = yes (app∥ x∥t x∥u)
x ∥? app t u | no  x∦t | _       = no (λ { (app∥ x∥t x∥u) → x∦t x∥t })
x ∥? app t u | _       | no  x∦u = no (λ { (app∥ x∥t x∥u) → x∦u x∥u })
