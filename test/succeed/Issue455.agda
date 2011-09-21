-- Andreas, 2011-09-12
-- eta for records in unifier

-- {-# OPTIONS -v tc.lhs.unify:25 #-}

module Issue455 where

postulate
  A : Set
  a : A

record Fork : Set where
  constructor pair
  field fst : A
        snd : A
open Fork

data D : Fork -> Set where
  c : (x y : A) -> D (pair x y)
  
postulate p : Fork

f : D p -> Set
f (c .(fst p) .(snd p)) = A  -- should work!

{- Unifier gives up on:
f z = {!z!}
Cannot decide whether there should be a case for the constructor c,
since the unification gets stuck on unifying the inferred indices
[pair x y] with the expected indices [p]
-}

record ⊤ : Set where
  constructor tt

data E : ⊤ -> Set where
  e : E tt

postulate q : ⊤

g : E q -> Set
g e = ⊤


