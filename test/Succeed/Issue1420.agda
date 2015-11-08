-- Andreas, 2015-02-07 Failed with-abstraction in rewrite-generated with.
-- {-# OPTIONS -v tc.rewrite.top:25 -v tc.with.top:25 -v tc.with.abstract:50 #-}

{-# OPTIONS --type-in-type #-}

module Issue1420 where

open import Common.Equality

postulate
  ▶    : Set → Set
  ▷    : ▶ Set → Set
  next : ∀{A}   → A → ▶ A
  _∗_  : ∀{A B} → ▶(A → B) → ▶ A → ▶ B

  ▶-def : ∀ A → ▷ (next A) ≡ ▶ A

  next∗ : ∀{A B : Set} (f : A → B) (a : A) →
          (next f ∗ next a) ≡ next (f a)

  Name : Set

data Tm : Set where
  name  : Name → Tm

data R : Tm → Set where
  name : ∀{x : Name} → R (name x)

print : Tm → ▶ Tm
print (name x) = next (name x)

-- Manually expanded with
test : ∀ (t : Tm) → ▷ (next R ∗ (print t))
test (name x) with next R ∗ next (name x) | next∗ R (name x)
... | ._ | refl rewrite ▶-def (R (name x)) = next name

-- Original rewrite
fails : ∀ (t : Tm) → ▷ (next R ∗ (print t))
fails (name x) rewrite next∗ R (name x) | ▶-def (R (name x)) = next name

-- should succeed
