------------------------------------------------------------------------
-- Convenient syntax for preorder proofs
------------------------------------------------------------------------

-- Example use:

-- n*0≡0 : forall n -> n * 0 ≡ 0
-- n*0≡0 zero    = ≡-refl
-- n*0≡0 (suc n) =
--     suc n * 0
--   ≃⟨ ≡-refl ⟩
--     n * 0 + 0
--   ≃⟨ n+0≡n (n * 0) ⟩
--     n * 0
--   ≃⟨ n*0≡0 n ⟩
--     0
--   ∎

-- I think that the idea behind this library is originally Ulf
-- Norell's. I have adapted it to my tastes and mixfix operators,
-- though.

open import Prelude.BinaryRelation

module Prelude.PreorderProof (p : PreSetoid) where

open import Prelude.Logic
private
  open module P   = PreSetoid p
  open module Pre = Preorder preorder

infix  2 _∎
infixr 2 _≃⟨_⟩_

abstract

  _≃⟨_⟩_ : forall x {y z} -> x ∼ y -> y ∼ z -> x ∼ z
  _ ≃⟨ x∼y ⟩ y∼z = trans x∼y y∼z

  _∎ : forall x -> x ∼ x
  _∎ _ = refl ≡-refl
