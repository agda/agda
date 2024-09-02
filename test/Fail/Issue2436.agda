-- Andreas, 2017-01-26, issue #2436
-- Outlaw coinductive records with eta-equality

{-# OPTIONS --guardedness #-}

record U : Set where
  coinductive
  eta-equality
  field f : U

-- Infinite eta-expansion would make Agda loop

test : U
test = _
