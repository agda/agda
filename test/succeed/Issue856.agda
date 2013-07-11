-- {-# OPTIONS -v tc.conv.inequal:20 #-}
module Issue856 where

import Common.Level

record ⊤ : Set where
data ⊥ : Set where

data Bool : Set where
  true  : Bool
  false : Bool

T : Bool → Set
T true  = ⊤
T false = ⊥

record ∃ {A : Set} (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

postulate
  G : Set → Set
  D : ∀ {A} → G A → A → Set

P : {A : Set} → G A → Set
P g = ∀ x → D g x

postulate
  f : ∀ {A} {g : G A} → P g → P g
  g : (p : ⊥ → Bool) → G (∃ λ t → T (p t))
  h : ∀ {p : ⊥ → Bool} {t pt} → D (g p) (t , pt)
  p : ⊥ → Bool

works : P (g p)
works = f (λ _ → h {p = p})

fails : P (g p)
fails = f (λ _ → h)
