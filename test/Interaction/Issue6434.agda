-- Andreas, 2023-01-13, issue #6434
-- With the following option, case splitting should not eliminate absurd clauses automatically.

{-# OPTIONS --no-infer-absurd-clauses #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

idTrue : ∀ b → b ≡ true → Bool
idTrue b eq = {!!}

-- C-c C-c b RET gives us:
-- idTrue false eq = {!!}
-- idTrue true eq = {!!}
