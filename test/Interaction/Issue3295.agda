module Issue3295 where

open import Issue3295.Incomplete
open import Issue3295.Incomplete2
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

_ : f 0 ≡ 0
_ = {!!}

_ : g 0 ≡ 0
_ = {!!}

_ : f 1 ≡ 1 -- the evaluation of `f` should be blocked here
_ = {!!}    -- so looking at the normalised type should not cause any issue

_ : g 1 ≡ 1 -- the evaluation of `g` should be blocked here
_ = {!!}    -- so looking at the normalised type should not cause any issue
