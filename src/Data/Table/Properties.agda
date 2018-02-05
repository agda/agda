------------------------------------------------------------------------
-- The Agda standard library
--
-- Table-related properties
------------------------------------------------------------------------

module Data.Table.Properties where

open import Data.Table
open import Data.Table.Relation.Equality

open import Data.Bool using (true; false; if_then_else_)
open import Data.Fin as Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.List as L using (List; _∷_; [])
open import Data.List.Any using (here; there; index)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Product as Product using (Σ; ∃; _,_; proj₁; proj₂)
open import Data.Vec as V using (Vec; _∷_; [])
import Data.Vec.Properties as VP
open import Function using (_∘_; flip)
open import Function.Inverse using (Inverse)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary.Decidable using (⌊_⌋)

module _ {a} {A : Set a} where

  fromList-∈ : ∀ {xs : List A} (i : Fin (L.length xs)) → lookup (fromList xs) i ∈ xs
  fromList-∈ {[]} ()
  fromList-∈ {x ∷ xs} Fin.zero = here P.refl
  fromList-∈ {x ∷ xs} (Fin.suc i) = there (fromList-∈ i)

  index-fromList-∈ : ∀ {xs i} → index (fromList-∈ {xs} i) ≡ i
  index-fromList-∈ {[]} {()}
  index-fromList-∈ {x ∷ xs} {Fin.zero} = P.refl
  index-fromList-∈ {x ∷ xs} {Fin.suc i} = P.cong Fin.suc index-fromList-∈

  fromList-index : ∀ {xs} {x : A} (x∈xs : x ∈ xs) → lookup (fromList xs) (index x∈xs) ≡ x
  fromList-index (here px) = P.sym px
  fromList-index (there x∈xs) = fromList-index x∈xs

  lookup∈ : ∀ {xs : List A} (i : Fin (L.length xs)) → ∃ λ x → x ∈ xs
  lookup∈ i = _ , fromList-∈ i

  private
    fromVec : ∀ {n} → Vec A n → Table A n
    fromVec = tabulate ∘ flip V.lookup

    toVec : ∀ {n} → Table A n → Vec A n
    toVec = V.tabulate ∘ lookup

    fromVec-toVec : ∀ {n} (t : Table A n) → fromVec (toVec t) ≗ t
    fromVec-toVec _ = VP.lookup∘tabulate _

    toVec-fromVec : ∀ {n} (v : Vec A n) → toVec (fromVec v) ≡ v
    toVec-fromVec = VP.tabulate∘lookup


  -- Isomorphism between tables and vectors.

  ↔Vec : ∀ {n} → Inverse (≡-setoid A n) (P.setoid (Vec A n))
  ↔Vec = record
    { to = record { _⟨$⟩_ = toVec ; cong = VP.tabulate-cong }
    ; from = P.→-to-⟶ fromVec
    ; inverse-of = record
      { left-inverse-of = VP.lookup∘tabulate ∘ lookup
      ; right-inverse-of = VP.tabulate∘lookup
      }
    }


  -- Selecting from any table is the same as selecting from a constant table.

  select-const : ∀ {n} (z : A) (i : Fin n) t → select z i t ≗ select z i (replicate (lookup t i))
  select-const z i t j with ⌊ j ≟ i ⌋
  select-const z i t j | true = P.refl
  select-const z i t j | false = P.refl
