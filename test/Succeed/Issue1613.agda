
postulate A : Set

record R : Set where
  constructor c
  field f : A

open R {{...}}

works : {{_ : R}} → A
works = f

works' : {{_ : R}} → Set → A
works' B = f

test : {{_ : R}} → A
test {{_}} = f

-- No variable of type R was found in scope.
-- when checking that the expression f has type A

test1 : {{_ : R}} → Set → A
test1 B = f

-- No variable of type R was found in scope.
-- when checking that the expression f has type A
