------------------------------------------------------------------------
-- A version of EqReasoning with an abstract equality type
------------------------------------------------------------------------

-- The equality type is abstract to make it possible to infer
-- arguments even if the underlying equality evaluates.

-- When this is not the case it may be preferable to use
-- Relation.Binary.EqReasoning, which does not hide the implementation
-- of the underlying equality, thus allowing more things to evaluate.

open import Relation.Binary

module Relation.Binary.EqReasoning.Abstract (p : Preorder) where

open import Logic
private
  open module P = PreorderOps p

infix  4 _equalTo_
infix  2 _∎
infixr 2 _∼⟨_⟩_ _≈⟨_⟩_
infix  1 begin_

abstract

  _equalTo_ : carrier -> carrier -> Set
  _equalTo_ = _∼_

  begin_ : forall {x y} -> x equalTo y -> x ∼ y
  begin_ eq = eq

  _∼⟨_⟩_ : forall x {y z} -> x ∼ y -> y equalTo z -> x equalTo z
  _ ∼⟨ x∼y ⟩ y∼z = trans x∼y y∼z

  _≈⟨_⟩_ : forall x {y z} -> x ≈ y -> y equalTo z -> x equalTo z
  _ ≈⟨ x≈y ⟩ y∼z = trans (refl x≈y) y∼z

  ≈-byDef : forall {x} -> x ≈ x
  ≈-byDef = Eq.refl ≡-refl

  byDef : forall {x} -> x ∼ x
  byDef = refl ≈-byDef

  _∎ : forall x -> x equalTo x
  _∎ _ = byDef
