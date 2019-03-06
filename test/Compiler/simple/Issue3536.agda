-- Issue 3536 reported by Malin Altenmüller

-- The problem was that the Treeless compiler reruns the clause
-- compiler, but without the split tree from the coverage
-- checker. However, the split tree is necessary to direct the clause
-- compiler.

data Unit : Set where
 true : Unit

record R : Set where
 coinductive
 field
   f1 : R
   f2 : R
open R public

foo : Unit -> R
f1 (foo true) = foo true
f2 (foo b) = foo b
