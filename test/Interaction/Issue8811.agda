-- Andreas, 2026-10-06, issue #8811, reported by @shhyou.
-- Giving a Pi type with unknown domain types failed with --prop
-- because the occurs check treated sort annotations as non-erased.

{-# OPTIONS --prop #-}

postulate
  A : Set
  Ω : Prop

B : Set
B = {! (a : ?) (b : ?) → A !}

p : Prop
p = {! (a : ?) (b : ?) → Ω !}
