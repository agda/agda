-- Andreas, 2022-12-04, issue #6380, reported by Felix Cherubini.

postulate
  B C : Set
  b   : B
  c   : C

record R : Set where
  instance
    irrelevantInstance = b

  something : C → C
  something c = c

postulate r : R
open R {{...}}

instance _ = r

_ =  something c
-- This used to trigger an InstanceWithExplicitArg warning.
