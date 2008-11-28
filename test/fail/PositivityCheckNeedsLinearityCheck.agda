-- This is an example emphasizing the important of a linearity check
-- in the positivity check.
--
-- Currently it does not type check since there is no universe subtyping.

module PositivityCheckNeedsLinearityCheck where

data Eq (S : Set2) : Set2 -> Set where
  refl : Eq S S

subst' : {S S' : Set2} -> Eq S S' -> S -> S'
subst' refl s = s

-- what happens if Eq is considered covariant in its first argument?
-- then because of subtyping,

p : Eq Set1 Set
p = refl

S : Set
S = subst' p Set

-- now S, which evaluates to Set, is in Set







