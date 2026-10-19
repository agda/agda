-- Andreas, 2016-05-03 issue #1950
-- testcases from issue #679

-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v reify.display:100 #-}
-- {-# OPTIONS -v tc.display.top:100 #-}

postulate anything : ∀{A : Set} → A
postulate Anything : ∀{A : Set1} → A

record ⊤ : Set where

data ty : Set where
  ♭ : ty
  _`→_ : ty → ty → ty

⟦_⟧ : ty → Set
⟦ ♭ ⟧ = ⊤
⟦ A `→ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧

eq : ∀ (σ : ty) (a b : ⟦ σ ⟧) → Set
eq ♭ a b = Anything
eq (A `→ B) f g = ∀ {a : ⟦ A ⟧} → eq B (f a) (g a)

eq-sym : ∀ σ {a b} (h : eq σ a b) → eq σ b a
eq-sym ♭ h = anything
eq-sym (A `→ B) h with B
... | B' = {!B'!}

-- splitting on B' should yield
-- eq-sym (A `→ B) h | ♭ = {!!}
-- eq-sym (A `→ B) h | B' `→ B'' = {!!}

data Unit : Set where
  unit : Unit

T : Unit → Set
T unit = {u : Unit} → Unit

fails : (u : Unit) → T u
fails unit with unit
... | q = {!q!}

-- Splitting on q should yield
-- fails unit | unit = {!!}
