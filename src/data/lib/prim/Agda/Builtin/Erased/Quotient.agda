------------------------------------------------------------------------
-- Set quotients with erased higher constructors and an eliminator
-- that computes for the point constructor
------------------------------------------------------------------------

-- The interface is based on the presentations of quotients in Martin
-- Hofmann's PhD thesis and the HoTT book, as well as the set quotient
-- HIT in the cubical library, due to Zesen Qian and Anders Mörtberg.

{-# OPTIONS --cubical-compatible --safe --no-sized-types
            --no-guardedness --level-universe --erased-quotients #-}

module Agda.Builtin.Erased.Quotient where

open import Agda.Builtin.Equality
open import Agda.Primitive

private variable
  a p r : Level
  A     : Set _
  @0 R  : A → A → Set _
  x y   : A

-- The property of being a set.

Is-set : Set a → Set a
Is-set A = {x y : A} (p q : x ≡ y) → p ≡ q

-- The subst function.

subst : (P : A → Set p) → x ≡ y → P x → P y
subst _ refl p = p

infix 4 _/_

postulate

  -- Set quotients.

  _/_ : (A : Set a) (@0 R : A → A → Set r) → Set (a ⊔ r)

  -- The point constructor.
  --
  -- If the type of [_] is changed, then
  -- Agda.TypeChecking.Primitive.primQrec might need to be modified.

  [_] : {a r : Level} {A : Set a} {@0 R : A → A → Set r} → A → A / R

  -- [_] respects the quotient relation.

  @0 resp : R x y → _≡_ {A = A / R} [ x ] [ y ]

  -- The quotients are set-truncated.

  @0 set : Is-set (A / R)

{-# BUILTIN QUOTIENTCONSTRUCTOR [_] #-}
{-# FOREIGN GHC type Quotient a r a' r' = a' #-}
{-# COMPILE GHC _/_ = type Quotient #-}
{-# COMPILE GHC [_] = \_ _ _ _ x -> x #-}
{-# COMPILE JS  [_] =  _ => _ => _ => _ => x => x #-}

primitive

  -- An eliminator for _/_.
  --
  -- If the type of qrec is changed, then
  -- Agda.TypeChecking.Primitive.primQrec and compiler backend code
  -- might need to be modified.

  qrec :
    {a r p : Level} {A : Set a} {@0 R : A → A → Set r}
    (P : A / R → Set p)
    (f : ∀ x → P [ x ]) →
    @0 (∀ {x y} (r : R x y) → subst P (resp r) (f x) ≡ f y) →
    @0 (∀ x → Is-set (P x)) →
    (x : A / R) → P x
