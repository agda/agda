-- Andreas, 2016-12-30, issue #2368 reported by m0davis

-- {-# OPTIONS -v interaction.give:100 -v tc.constr:30 #-}

open import Agda.Builtin.Reflection

macro
  mac : Term → Term → TC _
  mac = {!!}

foo : Set → Set → Set
foo = mac (foo {!Term!} {!Term!})  -- give both solutions

-- WAS: internal error after giving the second `Term`

-- Expected: yellow
