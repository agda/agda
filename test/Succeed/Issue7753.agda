-- Andreas, 2025-03-23, issue #7753
-- report and test case by Szumi Xie

open import Agda.Builtin.Bool

record Wrap : Set where
  field unwrap : Bool
open Wrap public

data F : Bool → Set where
  c1 : F true
  c2 : F true

G : Bool → Set
G true = Wrap
G false = Bool → Bool

h : (b : Bool) → F b → G b
h true c1 .unwrap = true
h .true c2 .unwrap = true  -- WAS: possible __IMPOSSIBLE__

-- Should succeed.
