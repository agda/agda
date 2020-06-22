
data ⊥ : Set where

record ⊤ : Set where
  constructor unit

data T : ⊥ → Set where
  con : (i : ⊥) → T i

module M (x : ⊤) where
  bar : (i : ⊥) → T i → ⊥
  bar .i (con i) = i
    module N where
      foo : ⊥
      foo = i

  -- Should not be accepted.
  -- Type signature should be `test : ⊥ → ⊥`
  test : ⊥ → ⊥
  test = N.foo

false : ⊥
false = M.test unit unit
