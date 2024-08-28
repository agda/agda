{-# OPTIONS --no-pattern-matching #-}

id : {A : Set} (x : A) → A
id x = x

data Unit : Set where
  unit : Unit

fail : Unit → Set
fail unit = Unit

-- Expected error: Pattern matching is disabled (use option --pattern-matching to enable it)
