------------------------------------------------------------------------
-- Convenient syntax for preorder proofs
------------------------------------------------------------------------

-- Example use:

-- n*0≡0 : forall n -> n * 0 ≡ 0
-- n*0≡0 zero    = ≡-refl
-- n*0≡0 (suc n) =
--   begin
--     suc n * 0
--   ∼⟨ byDef ⟩
--     n * 0 + 0
--   ∼⟨ n+0≡n _ ⟩
--     n * 0
--   ∼⟨ n*0≡0 n ⟩
--     0
--   ∎

-- I think that the idea behind this library is originally Ulf
-- Norell's. I have adapted it to my tastes and mixfix operators,
-- though.

open import Relation.Binary

module Relation.Binary.EqReasoning (p : PreSetoid) where

open import Logic
private
  open module P   = PreSetoid p
  open module Pre = Preorder preorder
  module E    = Equivalence equiv
  module EPre = Preorder E.preorder

infix  2 _∎
infixr 2 _∼⟨_⟩_ _≈⟨_⟩_
infix  1 begin_

begin_ : forall {x y} -> x ∼ y -> x ∼ y
begin_ eq = eq

_∼⟨_⟩_ : forall x {y z} -> x ∼ y -> y ∼ z -> x ∼ z
_ ∼⟨ x∼y ⟩ y∼z = trans x∼y y∼z

_≈⟨_⟩_ : forall x {y z} -> x ≈ y -> y ∼ z -> x ∼ z
_ ≈⟨ x≈y ⟩ y∼z = trans (refl x≈y) y∼z

≈-byDef : forall {x} -> x ≈ x
≈-byDef = EPre.refl ≡-refl

byDef : forall {x} -> x ∼ x
byDef = refl ≈-byDef

_∎ : forall x -> x ∼ x
_∎ _ = byDef
