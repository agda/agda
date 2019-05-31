{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

module _ where

data Unit : Set where
  unit : Unit

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

module _ (p : false ≡ true) where

  block : {A : Set} → Unit → A → A
  block unit x = x

  r : ∀ u → block u false ≡ true
  r unit = p

  {-# REWRITE r #-}

  r′ : ∀ u → block u false ≡ true
  r′ u = refl

  lazy : false ≡ true
  lazy = r′ unit

T : Bool → Set
T true  = Bool
T false = Bool → Bool

module _ (p : false ≡ true) where

  bool : (Bool → Bool) → Bool
  bool = subst T (lazy p)

  fun : Bool → (Bool → Bool)
  fun = subst T (sym (lazy p))

  omega : Bool → Bool
  omega = λ x → fun x x

  loop : Bool
  loop = omega (bool omega)

-- omega = λ p x → x x
-- loop = λ p → <BLACKHOLE>
