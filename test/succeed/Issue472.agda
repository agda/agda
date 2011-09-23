
module Issue472 where

postulate
 I : Set
 P : I → Set

record ∃ (P : I → Set) : Set where
 constructor _,_
 field
   fst : I
   snd : P fst

open ∃

data S : ∃ P → Set where
 s : (i : I) (x : P i) → S (i , x)

Foo : (p : ∃ P) → S p → Set
Foo p (s .(fst p) .(snd p)) = I

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Substitute.hs:47
