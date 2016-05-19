-- Andreas, 2016-05-19, issue 1986, after report from Nisse

record _×_ (A B : Set) : Set where
  constructor _,_
  field fst : A
        snd : B
open _×_

test : ∀{A : Set}(a : A) → A × A
fst (test a) = a
test a = {! a , a !}
-- SAME: test = λ a → {! a , a !}

-- This gives an internal error now, but should either give a proper
-- error message or "unsolved metas".
