{-# OPTIONS -v tc.lhs:50 #-}
{-# OPTIONS -v tc.coverage:50 #-}

open import Agda.Builtin.String

test : String → String
test x@"foo" = "bar"
test x       = x
