postulate
  S : Set
  instance s : S

record R : Set where
  field
    A     : S
    {B}   : S
    {{C}} : S

open R

r : R
r = {!!}
-- C-c C-c produced
-- A r = {!!}
-- B {r} = {!!}
-- C {{r}} = {!!}
