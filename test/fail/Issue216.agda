
-- Should fail with S i != i
module Issue216 where

open import Common.Level

Foo : {i : Level} → Set i
Foo {i} = (R : Set i) → R
