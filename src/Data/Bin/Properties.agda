------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the binary representation of natural numbers
------------------------------------------------------------------------

module Data.Bin.Properties where

open import Data.Bin
open import Data.Digit using (Bit)
import Data.Fin as Fin
import Data.Fin.Properties as 𝔽ₚ
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Properties using (∷-injective)
open import Data.Nat
  using (ℕ; zero; z≤n; s≤s; ≤-pred)
  renaming (suc to 1+_; _+_ to _+ℕ_; _*_ to _*ℕ_)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; isEquivalence; resp₂; decSetoid)
open import Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- (Bin, _≡_) is a decidable setoid

1#-injective : ∀ {as bs} → as 1# ≡ bs 1# → as ≡ bs
1#-injective refl = refl

infix 4 _≟_ _≟LB_

_≟LB_ : Decidable (_≡_ {A = List Bit})
_≟LB_ []       []       = yes refl
_≟LB_ []       (_ ∷ _)  = no λ()
_≟LB_ (_ ∷ _) []        = no λ()
_≟LB_ (x ∷ xs) (y ∷ ys) with x 𝔽ₚ.≟ y | xs ≟LB ys
... | _        | no xs≢ys = no (xs≢ys ∘ proj₂ ∘ ∷-injective)
... | no  x≢y  | _        = no (x≢y   ∘ proj₁ ∘ ∷-injective)
... | yes refl | yes refl = yes refl

_≟_ : Decidable {A = Bin} _≡_
0#    ≟ 0#    = yes refl
0#    ≟ bs 1# = no λ()
as 1# ≟ 0#    = no λ()
as 1# ≟ bs 1# with as ≟LB bs
... | yes refl  = yes refl
... | no  as≢bs = no (as≢bs ∘ 1#-injective)

≡-isDecEquivalence : IsDecEquivalence _≡_
≡-isDecEquivalence = record
  { isEquivalence = isEquivalence
  ; _≟_           = _≟_
  }

≡-decSetoid : DecSetoid _ _
≡-decSetoid = decSetoid _≟_

------------------------------------------------------------------------
-- (Bin _≡_ _<_) is a strict total order

<-trans : Transitive _<_
<-trans (less lt₁) (less lt₂) = less (ℕₚ.<-trans lt₁ lt₂)

<-asym : Asymmetric _<_
<-asym (less lt) (less gt) = ℕₚ.<-asym lt gt

<-irrefl : Irreflexive _≡_ _<_
<-irrefl refl (less lt) = ℕₚ.<-irrefl refl lt

∷ʳ-mono-< : ∀ {a b as bs} → as 1# < bs 1# → (a ∷ as) 1# < (b ∷ bs) 1#
∷ʳ-mono-< {a} {b} {as} {bs} (less lt) = less (begin
  1+ (m₁ +ℕ n₁ *ℕ 2) ≤⟨ s≤s (ℕₚ.+-mono-≤ (≤-pred (𝔽ₚ.bounded a)) ℕₚ.≤-refl) ⟩
  1+ (1 +ℕ n₁ *ℕ 2)  ≡⟨ refl ⟩
  1+ n₁ *ℕ 2         ≤⟨ ℕₚ.*-mono-≤ lt ℕₚ.≤-refl ⟩
  n₂ *ℕ 2            ≤⟨ ℕₚ.n≤m+n m₂ (n₂ *ℕ 2) ⟩
  m₂ +ℕ n₂ *ℕ 2      ∎)
  where
  open ℕₚ.≤-Reasoning
  m₁ = Fin.toℕ a;   m₂ = Fin.toℕ b
  n₁ = toℕ (as 1#); n₂ = toℕ (bs 1#)

∷ˡ-mono-< : ∀ {a b bs} → a Fin.< b → (a ∷ bs) 1# < (b ∷ bs) 1#
∷ˡ-mono-< {a} {b} {bs} lt = less (begin
  1 +ℕ (m₁  +ℕ n *ℕ 2)  ≡⟨ sym (ℕₚ.+-assoc 1 m₁ (n *ℕ 2)) ⟩
  (1 +ℕ m₁) +ℕ n *ℕ 2   ≤⟨ ℕₚ.+-mono-≤ lt ℕₚ.≤-refl ⟩
  m₂  +ℕ n *ℕ 2   ∎)
  where
  open ℕₚ.≤-Reasoning
  m₁ = Fin.toℕ a; m₂ = Fin.toℕ b; n = toℕ (bs 1#)

1<[23] : ∀ {b} → [] 1# < (b ∷ []) 1#
1<[23] {b} = less (ℕₚ.n≤m+n (Fin.toℕ b) 2)

1<2+ : ∀ {b bs} → [] 1# < (b ∷ bs) 1#
1<2+ {_} {[]}     = 1<[23]
1<2+ {_} {b ∷ bs} = <-trans 1<[23] (∷ʳ-mono-< {a = b} 1<2+)

0<1+ : ∀ {bs} → 0# < bs 1#
0<1+ {[]}     = less (s≤s z≤n)
0<1+ {b ∷ bs} = <-trans (less (s≤s z≤n)) 1<2+

<⇒≢ : ∀ {a b} → a < b → a ≢ b
<⇒≢ lt eq = asym⟶irr (resp₂ _<_) sym <-asym eq lt

<-cmp : Trichotomous _≡_ _<_
<-cmp 0#            0#            = tri≈ (<-irrefl refl) refl (<-irrefl refl)
<-cmp 0#            (_ 1#)        = tri< 0<1+ (<⇒≢ 0<1+) (<-asym 0<1+)
<-cmp (_ 1#)        0#            = tri> (<-asym 0<1+) (<⇒≢ 0<1+ ∘ sym) 0<1+
<-cmp ([] 1#)       ([] 1#)       = tri≈ (<-irrefl refl) refl (<-irrefl refl)
<-cmp ([] 1#)       ((b ∷ bs) 1#) = tri< 1<2+ (<⇒≢ 1<2+) (<-asym 1<2+)
<-cmp ((a ∷ as) 1#) ([] 1#)       = tri> (<-asym 1<2+) (<⇒≢ 1<2+ ∘ sym) 1<2+
<-cmp ((a ∷ as) 1#) ((b ∷ bs) 1#) with <-cmp (as 1#) (bs 1#)
... | tri<  lt ¬eq ¬gt =
  tri< (∷ʳ-mono-< lt)  (<⇒≢ (∷ʳ-mono-< lt)) (<-asym (∷ʳ-mono-< lt))
... | tri> ¬lt ¬eq  gt =
  tri> (<-asym (∷ʳ-mono-< gt)) (<⇒≢ (∷ʳ-mono-< gt) ∘ sym) (∷ʳ-mono-< gt)
... | tri≈ ¬lt refl ¬gt with 𝔽ₚ.cmp a b
...   | tri≈ ¬lt′ refl ¬gt′ =
  tri≈ (<-irrefl refl) refl (<-irrefl refl)
...   | tri<  lt′ ¬eq  ¬gt′ =
  tri< (∷ˡ-mono-< lt′)  (<⇒≢ (∷ˡ-mono-< lt′)) (<-asym (∷ˡ-mono-< lt′))
...   | tri> ¬lt′ ¬eq  gt′  =
  tri> (<-asym (∷ˡ-mono-< gt′)) (<⇒≢ (∷ˡ-mono-< gt′) ∘ sym) (∷ˡ-mono-< gt′)

<-isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
<-isStrictTotalOrder = record
  { isEquivalence = isEquivalence
  ; trans         = <-trans
  ; compare       = <-cmp
  }

<-strictTotalOrder : StrictTotalOrder _ _ _
<-strictTotalOrder = record
  { Carrier            = Bin
  ; _≈_                = _≡_
  ; _<_                = _<_
  ; isStrictTotalOrder = <-isStrictTotalOrder
  }
