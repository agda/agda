{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Issue6720 where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Cubical.Path

-- Reported by Dan Doel, minimised by Szumi Xie.
--
-- Conversion checking under --cubical can eliminate metas using
-- projections, without narrowing the meta's type.
--
-- The code below, we try to compute the sort of (essentially) fst _0,
-- where _0 : _1 is a meta-typed meta. For this we need to compute the
-- type of fst _0, but we can only infer the type of a projection
-- applied to a record. Since the blocker _1 was not handled, you got
-- fireworks instead.

postulate
  transport : {A B : Set} → A ≡ B → A → B
  cong : {A B : Set₁} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
  funExt⁻ :
    {A : Set} {B : A → Set₁} {f g : (x : A) → B x} → f ≡ g → (x : A) → f x ≡ g x

  A : Set
  F : A → Σ Set (λ _ → Set)

P : Set₁
P = _ -- F ≡ F

Q : A -> Set
Q = _ -- λ x → fst (F x)

f : (x : A) → P -> Q x -> fst (F x)
f x p q = transport (cong fst (funExt⁻ p x)) q -- transport (cong fst (funExt⁻ p x)) q
