-- Parameter arguments of overloaded projection applications
-- should not be skipped!

record R (A : Set) : Set where
  field f : A → A
open R

record S (A : Set) : Set where
  field f : A → A
open S

r : ∀{A} → R A
f r x = x

test : ∀{A : Set} → A → A
test a = f r a
