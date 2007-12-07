------------------------------------------------------------------------
-- Convenient syntax for "equational reasoning" using a preorder
------------------------------------------------------------------------

-- I think that the idea behind this library is originally Ulf
-- Norell's. I have adapted it to my tastes and mixfix operators,
-- though.

open import Relation.Binary

module Relation.Binary.PreorderReasoning (p : Preorder) where

open import Logic
open Preorder p

infix  4 _IsRelatedTo_
infix  2 _∎
infixr 2 _∼⟨_⟩_ _≈⟨_⟩_
infix  1 begin_

private

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

  data _IsRelatedTo_ (x y : carrier) : Set where
    relTo : x ∼ y -> x IsRelatedTo y

begin_ : forall {x y} -> x IsRelatedTo y -> x ∼ y
begin relTo x∼y = x∼y

_∼⟨_⟩_ : forall x {y z} -> x ∼ y -> y IsRelatedTo z -> x IsRelatedTo z
_ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

_≈⟨_⟩_ : forall x {y z} -> x ≈ y -> y IsRelatedTo z -> x IsRelatedTo z
_ ≈⟨ x≈y ⟩ relTo y∼z = relTo (trans (refl x≈y) y∼z)

≈-byDef : forall {x} -> x ≈ x
≈-byDef = Eq.refl ≡-refl

byDef : forall {x} -> x ∼ x
byDef = refl ≈-byDef

_∎ : forall x -> x IsRelatedTo x
_∎ _ = relTo byDef
