module Issue3295 where

open import Issue3295.Incomplete
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

_ : f 0 ≡ 0
_ = {!!}

_ : f 1 ≡ 1 -- the evaluation of `f` should be blocked here
_ = {!!}    -- so looking at the normalised type should not cause any issue
