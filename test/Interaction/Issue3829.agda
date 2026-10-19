-- Scenario:
--  * start with B only
--  * write 'f B = B'
--  * add constructor A
--  * want to deal with it first to preserve alphabetical ordering of clauses
--  * add 'f t = ?' *above* 'f B = B'

-- WAS: split t, get A and B
-- WANT: split t, get A only

data Type : Set where
  A B : Type

f : Type → Type
f t = {!!}
f B = B
