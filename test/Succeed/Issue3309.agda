-- Andreas, 2018-10-23, issue #3309 reported by G. Brunerie
--
-- Check that we can use irrelevant record fields in copattern matching.
--
-- (A refactoring broke the correct relevances of pattern variables
-- after matching on an irrelevant projection pattern.)

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    .snd : B fst
open Σ

pair : {A : Set} {B : A → Set} (a : A) .(b : B a) → Σ A B
pair a b .fst = a
pair a b .snd = b

f : {A : Set} {B : A → Set} (a : A) .(b : B a) → Σ A B
fst (f a b) = a
snd (f a b) = b

-- Should work.
