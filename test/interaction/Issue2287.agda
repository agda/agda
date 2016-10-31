
record R : Set₁ where
  field
    A     : Set
    {B}   : Set
    {{C}} : Set

open R

r : R
r = {!!}
-- C-c C-c produced
-- A r = {!!}
-- B {r} = {!!}
-- C {{r}} = {!!}
