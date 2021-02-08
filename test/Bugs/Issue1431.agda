
postulate
  A : Set
  P : A → Set
  a : A

  T    : Set → Set
  proj : (X : Set) → T X → X
  t    : T (∀ {x} → P x)

-- Checking target types first, prematurely solves the underscore with `P a` instead
-- of the correct `∀ {x} → P x`
fail : P a
fail = proj _ t
