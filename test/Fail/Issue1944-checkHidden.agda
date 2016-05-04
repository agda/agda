-- Andreas, AIM XXIII, 2016-04-25

-- Parameter arguments of overloaded projection applications
-- should not be skipped!

record R A : Set where
  field f : {x y : A} → A
open R

record S A : Set where
  field f : {x y : A} → A
open S

r : ∀{A} → R A
f r {x} = x

test : ∀{A B : Set} (a : A) (b : B) → A
test {A} a b = f (r {A}) {x = a} {y = b}
