-- Andreas, 2021-08-17, issue #5508, reported by james-smith-69781
-- On a case-insensitive file system, an inconsistency slipped into
-- the ModuleToSource map, leading to a failure in getting the module
-- name from the file name, in turn leading to a crash for certain errors.

module Issue5508 where -- case variant intended!

-- WAS: Crash in termination error

A : Set
A = A

record R : Set2 where
  field f : Set1

record S : Set2 where
  field g : Set1

record T : Set2 where
  field g : Set1

open S
open T
-- Now, g is ambiguous.

-- WAS: crash in "Cannot eliminate ... with projection" error

test : R
test .g = Set
