module Issue731 where

data empty : Set where

foo : empty → _
foo ()

bar : empty → Set
bar = foo

{- But when I want to know what are the constraints (C-c C-= in
emacs), I get the following error instead:

No binding for builtin thing LEVELZERO, use {-# BUILTIN LEVELZERO
name #-} to bind it to 'name'
when checking that the expression foo has type empty → Set

I’m not sure it is a bug, but it seems a bit strange to get an error
message when doing C-c C-= -}

-- Now displays correctly:
-- _4 := foo [blocked by problem 3]
-- [3] _2 =< Set : Set _1
-- _1 = (.Agda.Primitive.lsuc .Agda.Primitive.lzero)
-- _1 = (.Agda.Primitive.lsuc .Agda.Primitive.lzero)
