{-# OPTIONS --cubical --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat
open import Agda.Primitive.Cubical

module LocalRewriteRecordCubical where

module _ (n : Nat) (@rew p : n ≡ 0) where
  record Bar : Set where
