{-# OPTIONS --universe-polymorphism #-}

module Issue441 where

postulate
  Level : Set
  zero  : Level
  suc   : Level → Level
  _⊔_   : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}
-- {-# BUILTIN LEVELMAX  _⊔_   #-}  -- should yield a complaint that LEVELMAX isn't bound

infix 4 _≡_

data _≡_ {a} {A : Set a} : A → A → Set a where
  refl : ∀ x → x ≡ x

elim : ∀ {a p} {A : Set a} (P : {x y : A} → x ≡ y → Set p) →
       (∀ x → P (refl x)) →
       ∀ {x y} (x≡y : x ≡ y) → P x≡y
elim P r (refl x) = r _

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f (refl x) = refl (f x)

foo : ∀ {a} {A : Set a} {x y : A}
      (x≡y : x ≡ y) (f : x ≡ y → x ≡ y) →
      f x≡y ≡ f x≡y
foo = elim (λ {x} {y} x≡y → (f : x ≡ y → x ≡ y) → f x≡y ≡ f x≡y)
           (λ x f → cong {a = _} {b = _} f (refl (refl x)))
