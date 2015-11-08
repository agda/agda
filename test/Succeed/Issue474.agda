
module Issue474 where

open import Common.Level

postulate
  a b c : Level
  A : Set a
  B : Set b
  C : Set c

data Foo : Set (lsuc lzero ⊔ (a ⊔ (b ⊔ c))) where
  foo : (Set → A → B) → Foo
