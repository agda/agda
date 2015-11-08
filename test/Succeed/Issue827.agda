-- Andreas, 2013-03-22
-- cut down from  https://github.com/agda/agda-assoc-free/src/AssocFree/DList.agda
-- {-# OPTIONS -v tc.cover.splittree:10 -v tc.cc:30 #-}
module Issue827 where

open import Common.Equality

-- need to keep this record !
record List (A : Set) : Set where
  constructor list -- need to keep this constructor
  field bla : A

postulate
  _++_ : ∀ {A} → List A → List A → List A
  _∈_  : ∀ {A} (a : A) (as : List A) → Set
  _≪_ : ∀ {A} {a : A} {as} → (a ∈ as) → ∀ bs → (a ∈ (as ++ bs))
  _≫_ : ∀ {A} {a : A} as {bs} → (a ∈ bs) → (a ∈ (as ++ bs))

-- Case on membership

data Case {A} a (as bs : List A) : Set where
  inj₁ : (a∈as : a ∈ as) → Case a as bs
  inj₂ : (a∈bs : a ∈ bs) → Case a as bs

-- Three-way case, used for proving associativity properties

data Case₃ {A} (a : A) as bs cs : Set where
  inj₁ : (a ∈ as) → Case₃ a as bs cs
  inj₂ : (a ∈ bs) → Case₃ a as bs cs
  inj₃ : (a ∈ cs) → Case₃ a as bs cs

-- Associating case₃ to the right gives case

case : ∀ {A} {a : A} {as bs cs} → Case₃ a as bs cs → Case a as (bs ++ cs)
case {cs = cs} (inj₂ a∈bs) = inj₂ (a∈bs ≪ cs)
case {bs = bs} (inj₃ a∈cs) = inj₂ (bs ≫ a∈cs)
case           (inj₁ a∈as) = inj₁ a∈as

works : ∀ {A} {a : A} {as bs cs : List A} {a∈bs : a ∈ bs} →
  case {as = as} (inj₂ a∈bs) ≡ inj₂ (a∈bs ≪ cs)
works = refl

-- Different order of clauses fails:

case′ : ∀ {A} {a : A} {as bs cs} → Case₃ a as bs cs → Case a as (bs ++ cs)
case′           (inj₁ a∈as) = inj₁ a∈as
case′ {cs = cs} (inj₂ a∈bs) = inj₂ (a∈bs ≪ cs)
case′ {bs = bs} (inj₃ a∈cs) = inj₂ (bs ≫ a∈cs)

fails : ∀ {A} {a : A} {as bs cs : List A} {a∈bs : a ∈ bs} →
  case′ {as = as} (inj₂ a∈bs) ≡ inj₂ (a∈bs ≪ cs)
fails = refl

-- There was a bug in the record pattern translation.
-- Solution: expand all catch-alls in position of a record
-- pattern split.  Then record pattern translation works fine.
