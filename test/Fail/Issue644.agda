module Issue644 where

postulate
  A : Set

record R : Set₁ where
  field P : A → Set

module M₁ (r : R) where

  postulate
    Foo₁ : ((x : A) → R.P r x) → Set

module M₂ (r : R) where

  open R r

  postulate
    Foo₂ : ((x : A) → P x) → Set

postulate r : R

open R  r
open M₁ r
open M₂ r

foo₂ : Set
foo₂ = Foo₂ r

-- Error message should speak about
--
--   (x : A) → P x
--
-- not mention
--
--   (x : A) → .Bug.M₂._.P r x

