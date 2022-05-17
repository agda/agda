{-# OPTIONS --guarded #-}
module _ where

primitive
  primLockUniv : _

postulate
  A B : primLockUniv
  c : A → B
  foo : (@tick x y : B) → Set

bar2 : (@tick x : A) → Set
bar2 x = foo (c x) (c x)
