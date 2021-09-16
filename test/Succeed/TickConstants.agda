{-# OPTIONS --guarded #-}
module _ where

primitive
  primLockUniv : _

postulate
  A B : primLockUniv
  c : A → B
  foo : (@tick x y : B) → Set

bar : (@tick x y : A) → Set
bar x y = foo (c x) (c y)
