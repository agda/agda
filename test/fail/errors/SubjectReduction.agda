-- Based on an example due to Thorsten Altenkirch. See "Recursion with
-- boxes", http://sneezy.cs.nott.ac.uk/fplunch/weblog/?p=104.

module SubjectReduction where

Eq : {A : Set} → A → A → Set1
Eq {A} x y = (P : A → Set) → P x → P y

refl : ∀ {A} (x : A) → Eq x x
refl x P Px = Px

codata Stream : Set where
  tick : Stream → Stream

ticks : Stream
ticks = tick .ticks

l₁ : Eq ticks (tick ticks)
l₁ = refl ticks

l₂ : ∀ {s t} → Eq s t → Eq (tick s) (tick t)
l₂ eq = λ P Px → eq (λ s → P (tick s)) Px

Goal : Set1
Goal = Eq (tick ticks) (tick (tick ticks))

l₃ : Goal
l₃ = l₂ l₁

-- If l₃ is accepted, then it evaluates to λ P Px → Px, but the
-- following code is not accepted:

-- l₃′ : Goal
-- l₃′ = λ P Px → Px
