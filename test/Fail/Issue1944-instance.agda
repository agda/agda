-- Andreas, Issue 1944, Bengtfest Marsstrand 2016-04-28

-- A reason why issue 1098 (automatic opening of record modules)
-- cannot easily be fixed

data Bool : Set where
  true false : Bool

if_then_else_ : ∀{A : Set} → Bool → A → A → A
if true  then t else e = t
if false then t else e = e

record Testable (A : Set) : Set where
  field
    test : A -> Bool
open Testable {{...}}
open Testable  -- overloading projection `test`

mytest : ∀{A} → Testable A → A → Bool
mytest dict = test dict  -- Should work.

t : ∀{A}{{_ : Testable A}} → A → A
t = λ x → if test x then x else x
-- This may fail when test is overloaded.
