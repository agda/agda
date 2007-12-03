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

module Relation.Binary.EqReasoning (p : Preorder) where

open import Logic
open Preorder p

infix  4 _IsEqualTo_
infix  2 _∎
infixr 2 _∼⟨_⟩_ _≈⟨_⟩_
infix  1 begin_

private

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

  data _IsEqualTo_ (x y : carrier) : Set where
    eqTo : x ∼ y -> x IsEqualTo y

begin_ : forall {x y} -> x IsEqualTo y -> x ∼ y
begin eqTo x∼y = x∼y

_∼⟨_⟩_ : forall x {y z} -> x ∼ y -> y IsEqualTo z -> x IsEqualTo z
_ ∼⟨ x∼y ⟩ eqTo y∼z = eqTo (trans x∼y y∼z)

_≈⟨_⟩_ : forall x {y z} -> x ≈ y -> y IsEqualTo z -> x IsEqualTo z
_ ≈⟨ x≈y ⟩ eqTo y∼z = eqTo (trans (refl x≈y) y∼z)

≈-byDef : forall {x} -> x ≈ x
≈-byDef = Eq.refl ≡-refl

byDef : forall {x} -> x ∼ x
byDef = refl ≈-byDef

_∎ : forall x -> x IsEqualTo x
_∎ _ = eqTo byDef
