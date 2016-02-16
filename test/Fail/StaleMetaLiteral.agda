
module _ where

open import Common.Prelude hiding (_>>=_)
open import Common.Reflection
open import Common.Equality

open import Imports.StaleMetaLiteral

macro
  unquoteMeta : Meta → Tactic
  unquoteMeta m = give (meta m [])

thm : unquoteMeta staleMeta ≡ 42
thm = refl
