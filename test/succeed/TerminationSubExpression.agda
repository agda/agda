-- {-# OPTIONS -v term:20 #-}
-- Andreas, 2011-04-19 (Agda list post by Leonard Rodriguez)
module TerminationSubExpression where

open import Data.Nat

infixr 3 _⇨_
data Type : Set where
 int   : Type
 _⇨_   : Type → Type → Type

test : Type → ℕ
test int = 0
test (φ ⇨ int) = test φ
test (φ ⇨ (φ′ ⇨ φ″))  = test (φ′ ⇨ φ″)
-- this should work since subterm

test' : Type → ℕ
test' int = 0
test' (φ ⇨ int) = test' φ
test' (φ ⇨ φ′)  = test' φ′

ok : Type → ℕ
ok int = 0
ok (φ ⇨ φ′) with φ′
... | int = ok φ
... | (φ″ ⇨ φ‴) = ok (φ″ ⇨ φ‴)
