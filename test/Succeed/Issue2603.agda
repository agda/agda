-- Andreas, 2017-06-14, issue #2603
-- reported by rfindler, shrunk test case by Ulf

-- {-# OPTIONS -v tc.conv:40 -v tc.conv.atom:50 -v tc:80 -v tc.meta.assign:70 #-}

{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Equality

data List (A : Set) : Set where
  [] : List A

postulate
  Signal : Set

data Any (xs : List Signal) : Set where
  no : Any xs

any : ∀ xs → Any xs
any [] = no

record Env : Set where
  field sig : List Signal
open Env

Can : (θ : Env) → Any (sig θ) → Set
Can θ no = Signal

postulate
  elephant : ∀ θ → Can θ (any (sig θ)) ≡ Signal

lemma2 : Set
lemma2 rewrite elephant _ = Signal

-- Should succeed.
-- This lead to an internal error when the conversion checker
-- tried to eta expand a meta variable but dontAssignMetas was on.
