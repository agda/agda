------------------------------------------------------------------------
-- A data structure which keeps track of an upper bound on the number
-- of elements /not/ in a given list
------------------------------------------------------------------------

open import Relation.Binary

module Data.List.Countdown (D : DecSetoid) where

open import Data.Empty
open import Data.Fin using (Fin; zero; suc)
open import Data.Function
open import Data.List
open import Data.List.Any as Any using (here; there)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.FunctionSetoid
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; cong)
open PropEq.≡-Reasoning

private
  open module D = DecSetoid D
    hiding (refl) renaming (carrier to Elem)
  open Any.Membership D.setoid

------------------------------------------------------------------------
-- Helper functions

private

  drop-suc : ∀ {n} {i j : Fin n} →
             _≡_ {Fin (suc n)} (suc i) (suc j) → i ≡ j
  drop-suc refl = refl

  drop-inj₂ : ∀ {A B x y} → inj₂ {A} {B} x ≡ inj₂ y → x ≡ y
  drop-inj₂ refl = refl

  -- The /first/ occurrence of x in xs.

  first-occurrence : ∀ {xs} x → x ∈ xs → x ∈ xs
  first-occurrence x (here x≈y)           = here x≈y
  first-occurrence x (there {x = y} x∈xs) with x ≟ y
  ... | yes x≈y = here x≈y
  ... | no  _   = there $ first-occurrence x x∈xs

  -- The index of the first occurrence of x in xs.

  first-index : ∀ {xs} x → x ∈ xs → Fin (length xs)
  first-index x x∈xs = Any.index $ first-occurrence x x∈xs

  -- first-index preserves equality of its first argument.

  first-index-pres : ∀ {x₁ x₂ xs} (x₁∈xs : x₁ ∈ xs) (x₂∈xs : x₂ ∈ xs) →
                     x₁ ≈ x₂ → first-index x₁ x₁∈xs ≡ first-index x₂ x₂∈xs
  first-index-pres {x₁} {x₂} x₁∈xs x₂∈xs x₁≈x₂ = helper x₁∈xs x₂∈xs
    where
    helper : ∀ {xs} (x₁∈xs : x₁ ∈ xs) (x₂∈xs : x₂ ∈ xs) →
             first-index x₁ x₁∈xs ≡ first-index x₂ x₂∈xs
    helper (here x₁≈x) (here x₂≈x)           = refl
    helper (here x₁≈x) (there {x = x} x₂∈xs) with x₂ ≟ x
    ... | yes x₂≈x = refl
    ... | no  x₂≉x = ⊥-elim (x₂≉x (trans (sym x₁≈x₂) x₁≈x))
    helper (there {x = x} x₁∈xs) (here x₂≈x) with x₁ ≟ x
    ... | yes x₁≈x = refl
    ... | no  x₁≉x = ⊥-elim (x₁≉x (trans x₁≈x₂ x₂≈x))
    helper (there {x = x} x₁∈xs) (there x₂∈xs) with x₁ ≟ x | x₂ ≟ x
    ... | yes x₁≈x | yes x₂≈x = refl
    ... | yes x₁≈x | no  x₂≉x = ⊥-elim (x₂≉x (trans (sym x₁≈x₂) x₁≈x))
    ... | no  x₁≉x | yes x₂≈x = ⊥-elim (x₁≉x (trans x₁≈x₂ x₂≈x))
    ... | no  x₁≉x | no  x₂≉x = cong suc $ helper x₁∈xs x₂∈xs

  -- first-index is injective in its first argument.

  first-index-injective
    : ∀ {x₁ x₂ xs} (x₁∈xs : x₁ ∈ xs) (x₂∈xs : x₂ ∈ xs) →
      first-index x₁ x₁∈xs ≡ first-index x₂ x₂∈xs → x₁ ≈ x₂
  first-index-injective {x₁} {x₂} = helper
    where
    helper : ∀ {xs} (x₁∈xs : x₁ ∈ xs) (x₂∈xs : x₂ ∈ xs) →
             first-index x₁ x₁∈xs ≡ first-index x₂ x₂∈xs → x₁ ≈ x₂
    helper (here x₁≈x) (here x₂≈x)             _  = trans x₁≈x (sym x₂≈x)
    helper (here x₁≈x) (there {x = x} x₂∈xs)   _  with x₂ ≟ x
    helper (here x₁≈x) (there {x = x} x₂∈xs)   _  | yes x₂≈x = trans x₁≈x (sym x₂≈x)
    helper (here x₁≈x) (there {x = x} x₂∈xs)   () | no  x₂≉x
    helper (there {x = x} x₁∈xs) (here x₂≈x)   _  with x₁ ≟ x
    helper (there {x = x} x₁∈xs) (here x₂≈x)   _  | yes x₁≈x = trans x₁≈x (sym x₂≈x)
    helper (there {x = x} x₁∈xs) (here x₂≈x)   () | no  x₁≉x
    helper (there {x = x} x₁∈xs) (there x₂∈xs) _  with x₁ ≟ x | x₂ ≟ x
    helper (there {x = x} x₁∈xs) (there x₂∈xs) _  | yes x₁≈x | yes x₂≈x = trans x₁≈x (sym x₂≈x)
    helper (there {x = x} x₁∈xs) (there x₂∈xs) () | yes x₁≈x | no  x₂≉x
    helper (there {x = x} x₁∈xs) (there x₂∈xs) () | no  x₁≉x | yes x₂≈x
    helper (there {x = x} x₁∈xs) (there x₂∈xs) eq | no  x₁≉x | no  x₂≉x =
      helper x₁∈xs x₂∈xs (drop-suc eq)

  -- If there are at least two elements in Fin (suc n), then Fin n is
  -- inhabited. This is a variant of the thick function from Conor
  -- McBride's "First-order unification by structural recursion".

  thick : ∀ {n} (i j : Fin (suc n)) → i ≢ j → Fin n
  thick         zero     zero     i≢j = ⊥-elim (i≢j refl)
  thick         zero     (suc j)  _   = j
  thick {zero}  (suc ()) _        _
  thick {suc n} (suc i)  zero     _   = zero
  thick {suc n} (suc i)  (suc j)  i≢j =
    suc (thick i j (i≢j ∘ cong suc))

  -- thick i is injective in one of its arguments.

  thick-injective : ∀ {n} (i j k : Fin (suc n))
                    {i≢j : i ≢ j} {i≢k : i ≢ k} →
                    thick i j i≢j ≡ thick i k i≢k → j ≡ k
  thick-injective zero zero    _    {i≢j = i≢j} _   = ⊥-elim (i≢j refl)
  thick-injective zero _       zero {i≢k = i≢k} _   = ⊥-elim (i≢k refl)
  thick-injective zero (suc j) (suc k)          j≡k = cong suc j≡k
  thick-injective {zero}  (suc ()) _       _       _
  thick-injective {suc n} (suc i)  zero    zero    _ = refl
  thick-injective {suc n} (suc i)  zero    (suc k) ()
  thick-injective {suc n} (suc i)  (suc j) zero    ()
  thick-injective {suc n} (suc i)  (suc j) (suc k) eq =
    cong suc $ thick-injective i j k (drop-suc eq)

------------------------------------------------------------------------
-- The countdown data structure

-- If counted ⊕_n is inhabited then there are at most n values of type
-- Elem which are not members of counted (up to _≈_). You can read the
-- symbol _⊕_ as partitioning Elem into two parts: counted and
-- uncounted.

infix 4 _⊕_

record _⊕_ (counted : List Elem) (n : ℕ) : Set where
  field
    -- An element can be of two kinds:
    -- ⑴ It is provably in counted.
    -- ⑵ It is one of at most n elements which may or may not be in
    --   counted. The "at most n" part is guaranteed by the field
    --   "injective".

    kind      : ∀ x → x ∈ counted ⊎ Fin n
    injective : ∀ {x y i} → kind x ≡ inj₂ i → kind y ≡ inj₂ i → x ≈ y

-- A countdown can be initialised by proving that Elem is finite.

empty : ∀ {n} → Injection D.setoid (PropEq.setoid (Fin n)) → [] ⊕ n
empty inj =
  record { kind      = inj₂ ∘ _⟨$⟩_ to
         ; injective = λ {x} {y} {i} eq₁ eq₂ → injective (begin
             to ⟨$⟩ x  ≡⟨ drop-inj₂ eq₁ ⟩
             i         ≡⟨ PropEq.sym $ drop-inj₂ eq₂ ⟩
             to ⟨$⟩ y  ∎)
         }
  where open Injection inj

-- A countdown can also be initialised by proving that Elem is finite.

emptyFromList : (counted : List Elem) → (∀ x → x ∈ counted) →
                [] ⊕ length counted
emptyFromList counted complete = empty record
  { to = record
    { _⟨$⟩_ = λ x → first-index x (complete x)
    ; pres  = first-index-pres (complete _) (complete _)
    }
  ; injective = first-index-injective (complete _) (complete _)
  }

-- Finds out if an element has been counted yet.

lookup : ∀ {counted n} → counted ⊕ n → ∀ x → Dec (x ∈ counted)
lookup {counted} _ x = Any.any (_≟_ x) counted

-- When no element remains to be counted all elements have been
-- counted.

lookup! : ∀ {counted} → counted ⊕ zero → ∀ x → x ∈ counted
lookup! counted⊕0 x with _⊕_.kind counted⊕0 x
... | inj₁ x∈counted = x∈counted
... | inj₂ ()

private

  -- A variant of lookup!.

  lookup‼ : ∀ {m counted} →
            counted ⊕ m → ∀ x → x ∉ counted → ∃ λ n → m ≡ suc n
  lookup‼ {suc m} counted⊕n x x∉counted = (m , refl)
  lookup‼ {zero}  counted⊕n x x∉counted =
    ⊥-elim (x∉counted $ lookup! counted⊕n x)

-- Counts a previously uncounted element.

insert : ∀ {counted n} →
         counted ⊕ suc n → ∀ x → x ∉ counted → x ∷ counted ⊕ n
insert {counted} {n} counted⊕1+n x x∉counted =
  record { kind = kind′; injective = inj }
  where
  open _⊕_ counted⊕1+n

  helper : ∀ x y i {j} →
           kind x ≡ inj₂ i → kind y ≡ inj₂ j → i ≡ j → x ≈ y
  helper _ _ _ eq₁ eq₂ refl = injective eq₁ eq₂

  kind′ : ∀ y → y ∈ x ∷ counted ⊎ Fin n
  kind′  y with y ≟ x | kind x | kind y | helper x y
  kind′  y | yes y≈x | _              | _              | _   = inj₁ (here y≈x)
  kind′  y | _       | inj₁ x∈counted | _              | _   = ⊥-elim (x∉counted x∈counted)
  kind′  y | _       | _              | inj₁ y∈counted | _   = inj₁ (there y∈counted)
  kind′  y | no  y≉x | inj₂ i         | inj₂ j         | hlp =
    inj₂ (thick i j (y≉x ∘ sym ∘ hlp _ refl refl))

  inj : ∀ {y z i} → kind′ y ≡ inj₂ i → kind′ z ≡ inj₂ i → y ≈ z
  inj {y} {z} eq₁ eq₂ with y ≟ x | z ≟ x | kind x | kind y | kind z
                         | helper x y | helper x z | helper y z
  inj ()  _   | yes _ | _     | _              | _      | _      | _ | _ | _
  inj _   ()  | _     | yes _ | _              | _      | _      | _ | _ | _
  inj _   _   | no  _ | no  _ | inj₁ x∈counted | _      | _      | _ | _ | _ = ⊥-elim (x∉counted x∈counted)
  inj ()  _   | no  _ | no  _ | inj₂ _         | inj₁ _ | _      | _ | _ | _
  inj _   ()  | no  _ | no  _ | inj₂ _         | _      | inj₁ _ | _ | _ | _
  inj eq₁ eq₂ | no  _ | no  _ | inj₂ _         | inj₂ _ | inj₂ _ | _ | _ | hlp =
    hlp _ refl refl $
      thick-injective _ _ _ $
        PropEq.trans (drop-inj₂ eq₁) (PropEq.sym (drop-inj₂ eq₂))

-- Counts an element if it has not already been counted.

lookupOrInsert : ∀ {counted m} →
                 counted ⊕ m →
                 ∀ x → x ∈ counted ⊎
                       ∃ λ n → m ≡ suc n × x ∷ counted ⊕ n
lookupOrInsert counted⊕n x with lookup counted⊕n x
... | yes x∈counted = inj₁ x∈counted
... | no  x∉counted with lookup‼ counted⊕n x x∉counted
...   | (n , refl) = inj₂ (n , refl , insert counted⊕n x x∉counted)
