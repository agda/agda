-- Andreas, 2014-08-19, issue reported by zcarterc
-- {-# OPTIONS -v tc.meta.assign:10 -v tc.constr.findInScope:10 #-}
-- {-# OPTIONS -v tc.constr.findInScope:49 #-}
-- {-# OPTIONS --show-implicit #-}
module Issue1254 where

open import Agda.Primitive

record Inhabited {i : Level} (carrier : Set i) : Set i where
  field
    elem : carrier

open Inhabited {{...}}

record Wrap {i : Level} (carrier : Set i) : Set i where
  field
    wrap-inhabited : Inhabited carrier

instance
  wrap-as-inhabited : ∀ {i : Level} {carrier : Set i} {{cat : Wrap carrier}} → Inhabited carrier
  wrap-as-inhabited {{cat}} = Wrap.wrap-inhabited cat

postulate
  Nat : Set
  one : Nat

instance
  monoid-Nat : Wrap Nat
  monoid-Nat = record { wrap-inhabited = record { elem = one } }

-- This is what caused the crash.
op : Nat
op = elem
