{-# OPTIONS --allow-unsolved-metas #-}
module _ where

open import Common.Prelude
open import Common.Equality

foo : 0 ≡ 0
foo = refl

error : (x : 1 ≡ 1) → x ≡ refl
error x with foo
error x | y = {!!}
