{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

variable A : Set

postulate
  f : (A → A) → Bool
  f-id    :           f {A} (λ x → x) ≡ true
  f-const : (c : A) → f     (λ x → c) ≡ false

{-# REWRITE f-id    #-}
{-# REWRITE f-const #-}
