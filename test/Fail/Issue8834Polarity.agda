-- Andreas, 2026-10-15, issue #8834
-- Polarity of module parameters was not checked
-- when inserting them into the telescope of a definition.
-- This allowed a negative type constructor to be declared strictly positive.

{-# OPTIONS --polarity #-}

module Issue8834Polarity where

data ⊥ : Set where

data Fix (F : @++ Set → Set) : Set where
  inn : F (Fix F) → Fix F

-- A bug in the handling of polarity in telescopes
-- lets us define a type constructor C A ≅ A → ⊥
-- deemed strictly positive.

module M (@++ A : Set) where

  data Wrap : Set where
    wrap : A → Wrap

  C : Set
  C = Wrap → ⊥            -- uses A negatively, should be rejected

F : @++ Set → Set
F A = M.C A               -- accepted with wrong polarity

-- The rest is the usual exploit of negative types
-- by encoding of Ω = (λ x → x x) (λ x → x x).

D = Fix F

abs : (D → ⊥) → D
abs f = inn λ where
  (M.wrap d) → f d

app : D → D → ⊥
app (inn f) d = f (M.wrap d)

ω : D
ω = abs (λ d → app d d)

Ω : ⊥
Ω = app ω ω
