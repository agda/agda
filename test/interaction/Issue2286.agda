-- Andreas, 2016-10-30, issue #2286 reported by carlostome

-- {-# OPTIONS -v interaction.give:40 #-}
-- {-# OPTIONS -v tc.term.expr:40 #-}
-- {-# OPTIONS -v tc.meta:40 #-}

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x

f : Nat -> Nat
f x = {! f x !}  -- giving  f x  here used to loop, as termination checking was not redone

p1 : (n : Nat) -> f n == n
p1 n = refl  -- This unsolved constraint triggered the loop.
