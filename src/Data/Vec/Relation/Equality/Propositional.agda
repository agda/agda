------------------------------------------------------------------------
-- The Agda standard library
--
-- Vector equality over propositional equality
------------------------------------------------------------------------

open import Relation.Binary

module Data.Vec.Relation.Equality.Propositional {a} {A : Set a} where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Vec
import Data.Vec.Relation.Equality.Setoid as SEq
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

------------------------------------------------------------------------
-- Publically re-export everything from setoid equality

open SEq (setoid A) public

------------------------------------------------------------------------
-- ≋ is propositional

≋⇒≡ : ∀ {n} {xs ys : Vec A n} → xs ≋ ys → xs ≡ ys
≋⇒≡ []               = refl
≋⇒≡ (refl ∷ xs≈ys) = cong (_∷_ _) (≋⇒≡ xs≈ys)

≡⇒≋ : ∀ {n} {xs ys : Vec A n} → xs ≡ ys → xs ≋ ys
≡⇒≋ refl = ≋-refl

≋⇒≅ : ∀ {m n} {xs : Vec A m} {ys : Vec A n} →
          xs ≋ ys → xs ≅ ys
≋⇒≅ p with length-equal p
... | refl = H.≡-to-≅ (≋⇒≡ p)
