
open import Agda.Builtin.Equality

cong : ∀ {A B : Set} → (f : A → B) → ∀ {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

data ⊥ : Set where

data N : Set where
  ze : N
  su : (⊥ → N) → N

foo : N
foo = su (\ ())

postulate
  ext : ∀ {A : Set} → (f g : ⊥ → A) → f ≡ g

foo-suc : foo ≡ su (\ _ → foo)
foo-suc = cong su (ext (λ ()) (λ _ → foo))

-- bad!
no-cycle : ∀ {n} → n ≡ su (\ _ → n) → ⊥
no-cycle ()

false : ⊥
false = no-cycle foo-suc
