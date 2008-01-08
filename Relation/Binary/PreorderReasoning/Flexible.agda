------------------------------------------------------------------------
-- Convenient syntax for "equational reasoning" using a preorder
------------------------------------------------------------------------

-- A variant of Relation.Binary.PreorderReasoning which makes it
-- possible to open the module once, but still use it with different
-- preorders. The downside is that the preorder has to be given once
-- for every proof.

-- I don't think we should have two almost identical modules for
-- preorder reasoning in this library. Don't be surprised if one of
-- these modules disappears in the future.

module Relation.Binary.PreorderReasoning.Flexible where

open import Relation.Binary

infix  4 Under_,_IsRelatedTo_
infix  2 _∎
infixr 2 _∼⟨_⟩_ _≈⟨_⟩_
infix  1 proofWith_∶_

private

  data Under_,_IsRelatedTo_ (p : Preorder) (x y : Preorder.carrier p)
         : Set where
    relTo : let open Preorder p in x ∼ y -> Under p , x IsRelatedTo y

proofWith_∶_ : forall p -> let open Preorder p in
               {x y : carrier} -> Under p , x IsRelatedTo y -> x ∼ y
proofWith _ ∶ relTo x∼y = x∼y

_∼⟨_⟩_ : forall {p} -> let open Preorder p in forall x {y z} ->
         x ∼ y -> Under p , y IsRelatedTo z -> Under p , x IsRelatedTo z
_∼⟨_⟩_ {p} _ x∼y (relTo y∼z) = relTo (trans x∼y y∼z)
  where open Preorder p

_≈⟨_⟩_ : forall {p} -> let open Preorder p in forall x {y z} ->
         x ≈ y -> Under p , y IsRelatedTo z -> Under p , x IsRelatedTo z
_≈⟨_⟩_ {p} _ x≈y (relTo y∼z) = relTo (trans (refl x≈y) y∼z)
  where open Preorder p

_∎ : forall {p} x -> Under p , x IsRelatedTo x
_∎ {p} _ = relTo (refl Eq.refl)
  where open Preorder p
