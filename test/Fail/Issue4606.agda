{-# OPTIONS --cubical #-}

module Issue4606 where

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical

-- Test case from Andrew Pitts.
----------------------------------------------------------------------
-- Well-Founded Recursion
----------------------------------------------------------------------
data Acc {A : Set}(R : A → A → Set)(x : A) : Set where
  acc : (∀ y → R y x → Acc R y) → Acc R x

iswf : {A : Set}(R : A → A → Set) → Set
iswf R = ∀ x → Acc R x

----------------------------------------------------------------------
-- A logical contradiction
----------------------------------------------------------------------
data A : Set where
  O : A
  S : A → A
  E : ∀ x → S x ≡ x

data _<_ (x : A) : A → Set where
  <S : x < S x

O<O : O < O
O<O = primTransp (\ i →  O < E O i) i0 <S

-- Given that O < O holds, we should not be able to prove that < is
-- well-founded, but we can!
iswf< : iswf _<_
iswf< i = acc (α i)
  where
  α : ∀ x y → y < x → Acc _<_ y
 -- I don't think the following clause should pass
 -- the termination checker
  α .(S y) y <S = acc (α y)

data ⊥ : Set where

AccO→⊥ : Acc _<_ O → ⊥
AccO→⊥ (acc f) = AccO→⊥ (f O O<O)

contradiction : ⊥
contradiction = AccO→⊥ (iswf< O)
