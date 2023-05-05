{-# OPTIONS --hidden-argument-puns #-}

import Agda.Builtin.Bool as Bool

-- The following code should be rejected, because true is a
-- constructor, which is not in scope, of type Bool.Bool.

-- The error message should be pretty-printed correctly, using
-- {true} or {true = true} and {(A)}.

f : {true : Bool.Bool} {_ : Set} → Bool.Bool
f {true} {(A)} = true
