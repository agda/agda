
-- There was a rare bug in display form generation for with functions
-- in local blocks.

module WithInWhere where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

data Z? : Nat -> Set where
  yes : Z? zero
  no  : forall {n} -> Z? (suc n)

z? : (n : Nat) -> Z? n
z? zero    = yes
z? (suc n) = no

bug : Nat -> Nat
bug n = ans
  where
    ans : Nat
    ans with z? (suc n)
    ... | no with zero
    ...   |  _ = zero
