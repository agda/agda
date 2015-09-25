-- 2010-09-29 Andreas, mail to Ulf

module ExistentialsProjections where

postulate
 .irrelevant : {A : Set} -> .A -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor exists
  field
    .fwitness : A
    fcontent : P fwitness

.witness : forall {A P} -> (x : Exists A P) -> A
witness (exists a p) = irrelevant a

-- second projection out of existential is breaking abstraction, so should be forbidden

content : forall {A P} -> (x : Exists A P) -> P (witness x)
content (exists a p) = p  -- should not typecheck!!

{- We have p : P a != P (witness (exists a p)) = P (irrelevant a)
because a != irrelevant a.
-}
