open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Level

module IndexedMap
         {Index : Set} {Key : Index → Set} {_≈_ _<_ : Rel (∃ Key) zero}
         (isOrderedKeySet : IsStrictTotalOrder _≈_ _<_)
         -- Equal keys must have equal indices.
         (indicesEqual : _≈_ =[ proj₁ ]⇒ _≡_)
         (Value : Index → Set)
         where
