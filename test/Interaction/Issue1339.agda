-- Andreas, 2014-11-02

{-# OPTIONS --guardedness #-}

record U : Set where
  coinductive
  constructor inn
  field       out : U

f : U → U
f u = {!u!}
