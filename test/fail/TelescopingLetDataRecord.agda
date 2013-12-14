module _ where

module Batch4 where
  data D1 (open Star) (A : ★) : ★ where
    c : (x : A) → D1 A

  data D2 (open Star) : ★ where

  data D3 (open Star) : ★₁ where
    c : (A : ★) → D3

  data D4 : (open Star) → ★ where

  data D0 (A : Set) (let B = A → A) : B → Set where
    c : (f : B) → D0 A f

  module _ where

    data D5 (open Star) (A : ★) (open MEndo A) : ★

    data D5 A (open MEndo A) where
      c : (f : Endo) → D5 A

  data D6 (open Star) (A : ★) (open MEndo A) : Endo → ★ where
    c : (f : Endo) → D6 A f

module Batch5 where
  data D1 (open Star) (A : ★) : ★

  data D1 A where
    c : (x : A) → D1 A

  data D2 (open Star) : ★
  data D2 where

  data D3 (open Star) : ★₁
  data D3 where
    c : (A : ★) → D3

  data D4 : (open Star) → ★
  data D4 where

open import Common.Equality

module Batch6 where

  BinOp : (A : Set) → Set
  BinOp A = A → A → A

  record IsAssoc {A : Set} (_∘_ : BinOp A) : Set where
    field
      assoc : ∀ {a b c} →
        ((a ∘ b) ∘ c) ≡ (a ∘ (b ∘ c))

  record RawSemiGroup : Set₁ where
    field
      Carrier : Set
      _∘_     : Carrier → Carrier → Carrier

  record SemiGroupLaws1 (G : RawSemiGroup) : Set where
    open RawSemiGroup G
    field
      isAssoc : IsAssoc _∘_

  module _ where
   record SemiGroupBLA
      (G : RawSemiGroup)
      (open RawSemiGroup G)
      (ass : IsAssoc _∘_) : Set
    where

  record SemiGroupLaws (G : RawSemiGroup) (open RawSemiGroup G) : Set where
    field
      isAssoc : IsAssoc {A = Carrier} _∘_

  record SemiGroup : Set₁ where
    field
      rawSemiGroup  : RawSemiGroup
      semiGroupLaws : SemiGroupLaws rawSemiGroup
