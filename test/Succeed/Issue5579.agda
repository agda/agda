{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
open import Agda.Builtin.Bool

postulate
  Index : Set
  i     : Index

data D : Index →  Set where
  c : D i

cong : {A B : Set} (x y : A) (f : A → B) → x ≡ y → f x ≡ f y
cong _ _ f x≡y = λ i → f (x≡y i)

refl : {A : Set} {x : A} → x ≡ x
refl {x = x} = λ _ → x

subst :
  {A : Set} {x y : A}
  (P : A → Set) → x ≡ y → P x → P y
subst P eq p = primTransp (λ i → P (eq i)) i0 p

postulate
  subst-refl :
    {A : Set} {x : A} (P : A → Set) {p : P x} →
    subst P refl p ≡ p

f : {i : Index} (xs : D i) → D i
f c = c


works : f (subst D refl c) ≡ c
works = cong (subst D refl c) c f (subst-refl D)

-- There is no type error here, just a meta to solve.
-- The original problem was assuming injectivity of f.
should-work-too : f (subst D refl c) ≡ c
should-work-too = cong _ _ f (subst-refl D)
