{-# OPTIONS --prop #-}

postulate
  P : Prop
  p : P

-- C-c C-n should print `p` as `_`

record Box (X : Prop) : Set where
  constructor box
  field unbox : X
open Box

test : P → Box P
test = λ x → box x

-- C-c C-n should print `test` as `λ x → box _`
