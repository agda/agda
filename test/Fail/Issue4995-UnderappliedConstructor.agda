open import Agda.Builtin.Equality

data ⊥ : Set where

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

postulate
  funExt : ∀ {A B : Set} {f g : A → B}
         → (∀ x → f x ≡ g x) → f ≡ g

data D : Set where
  c1 : D → ⊥ → D
  c2 : (⊥ → D) → D

cycle : ∀ {n} → c2 (c1 n) ≡ n → ⊥
cycle ()

d : D
d = c2 λ ()

only-one-D : (x : D) → x ≡ d
only-one-D (c2 x) = cong c2 (funExt (λ ()))

boom : ⊥
boom = cycle (only-one-D (c2 (c1 d)))
