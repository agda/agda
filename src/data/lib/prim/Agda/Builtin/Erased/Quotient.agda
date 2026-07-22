------------------------------------------------------------------------
-- Set quotients with erased higher constructors and an eliminator
-- that computes for the point constructor
------------------------------------------------------------------------

-- The interface is based on the presentations of quotients in Martin
-- Hofmann's PhD thesis and the HoTT book, as well as the set quotient
-- HIT in the cubical library, due to Zesen Qian and Anders Mörtberg.

-- The implementation uses Dan Licata's trick.

{-# OPTIONS --cubical-compatible --safe --no-sized-types
            --no-guardedness --level-universe --polarity
            --erased-quotients #-}

module Agda.Builtin.Erased.Quotient where

open import Agda.Builtin.Equality
open import Agda.Primitive

private variable
  a p  : Level
  A    : Set _
  @0 R : A → A → Set _
  x y  : A

-- The property of being a set.

Is-set : Set a → Set a
Is-set A = {x y : A} (p q : x ≡ y) → p ≡ q

-- The subst function.

subst : (P : A → Set p) → x ≡ y → P x → P y
subst _ refl p = p

private module Quotient where

  -- Quotients.
  --
  -- The implementation is hidden so that users cannot match directly
  -- on the constructor.
  --
  -- The parameters have the @mixed annotation because that is the
  -- only polarity annotation that is accepted for the corresponding
  -- set quotient HIT implemented in Cubical Agda.

  infix 4 _/_

  data _/_ {@mixed a r} (@mixed A : Set a)
         (@0 @mixed R : A → A → Set r) : Set (a ⊔ r) where
    [_] : A → A / R

open Quotient public using (_/_)

-- The point constructor.

[_] : A → A / R
[_] = Quotient.[_]

postulate

  -- [_] respects the quotient relation.

  @0 resp : R x y → _≡_ {A = A / R} [ x ] [ y ]

  -- The quotients are set-truncated.

  @0 set  : Is-set (A / R)

-- An eliminator for _/_.

qrec :
  (P : A / R → Set p)
  (f : ∀ x → P [ x ]) →
  @0 (∀ {x y} (r : R x y) → subst P (resp r) (f x) ≡ f y) →
  @0 (∀ x → Is-set (P x)) →
  (x : A / R) → P x
qrec _ f _ _ Quotient.[ x ] = f x
