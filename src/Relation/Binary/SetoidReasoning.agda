------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" in multiple Setoids
------------------------------------------------------------------------

-- Example use:
--
--   open import Data.Maybe
--   import Relation.Binary.SetoidReasoning as SetR
--
--   begin⟨ S ⟩
--     x
--       ≈⟨ drop-just (begin⟨ setoid S ⟩
--          just x
--            ≈⟨ justx≈mz ⟩
--          mz
--            ≈⟨ mz≈justy ⟩
--          just y ∎) ⟩
--     y
--       ≈⟨ y≈z ⟩
--     z ∎

open import Relation.Binary.EqReasoning as EqR using (_IsRelatedTo_)
open import Relation.Binary
open import Relation.Binary.Core

open Setoid

module Relation.Binary.SetoidReasoning where

infix 1 begin⟨_⟩_
infixr 2 _≈⟨_⟩_ _≡⟨_⟩_
infix 3 _∎

begin⟨_⟩_ : ∀ {c l} (S : Setoid c l) → {x y : Carrier S} → _IsRelatedTo_ S x y → _≈_ S x y
begin⟨_⟩_ S p = EqR.begin_ S p

_∎ : ∀ {c l} {S : Setoid c l} → (x : Carrier S) → _IsRelatedTo_ S x x
_∎ {S = S} = EqR._∎ S

_≈⟨_⟩_ : ∀ {c l} {S : Setoid c l} → (x : Carrier S) → {y z : Carrier S} → _≈_ S x y → _IsRelatedTo_ S y z → _IsRelatedTo_ S x z
_≈⟨_⟩_ {S = S} = EqR._≈⟨_⟩_ S

_≡⟨_⟩_ : ∀ {c l} {S : Setoid c l} → (x : Carrier S) → {y z : Carrier S} → x ≡ y → _IsRelatedTo_ S y z → _IsRelatedTo_ S x z
_≡⟨_⟩_ {S = S} = EqR._≡⟨_⟩_ S
