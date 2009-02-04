------------------------------------------------------------------------
-- Some properties related to Data.Star
------------------------------------------------------------------------

module Data.Star.Properties where

open import Data.Star
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl; cong)
import Relation.Binary.PreorderReasoning as PreR

◅◅-assoc : ∀ {I} {T : Rel I} {i j k l}
                  (xs : Star T i j) (ys : Star T j k)
                  (zs : Star T k l) →
           (xs ◅◅ ys) ◅◅ zs ≡ xs ◅◅ (ys ◅◅ zs)
◅◅-assoc ε        ys zs = refl
◅◅-assoc (x ◅ xs) ys zs = cong (_◅_ x) (◅◅-assoc xs ys zs)

-- Reflexive transitive closures are preorders.

preorder : ∀ {I} (T : Rel I) → Preorder
preorder {I} T = record
  { carrier    = I
  ; _≈_        = _≡_
  ; _∼_        = Star T
  ; isPreorder = record
    { isEquivalence = PropEq.isEquivalence
    ; reflexive     = reflexive
    ; trans         = _◅◅_
    ; ≈-resp-∼      = PropEq.resp (Star T)
    }
  }
  where
  reflexive : _≡_ ⇒ Star T
  reflexive refl = ε

-- Preorder reasoning for Star.

module StarReasoning {I : Set} (T : Rel I) where
  open PreR (preorder T) public
    renaming (_∼⟨_⟩_ to _⟶⋆⟨_⟩_)

  infixr 2 _⟶⟨_⟩_

  _⟶⟨_⟩_ : ∀ x {y z} → T x y → y IsRelatedTo z → x IsRelatedTo z
  x ⟶⟨ x⟶y ⟩ y⟶⋆z = x ⟶⋆⟨ x⟶y ◅ ε ⟩ y⟶⋆z
