-- Copatterns disabled!
{-# OPTIONS --no-copatterns #-}

open import Common.Sigma

test : {A B : Set} (a : A) (b : B) → A × B
test a b = {!!}
-- Should give error when attempting to split.
