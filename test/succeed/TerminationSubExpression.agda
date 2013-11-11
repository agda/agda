-- {-# OPTIONS -v term:20 #-}
-- Andreas, 2011-04-19 (Agda list post by Leonard Rodriguez)
module TerminationSubExpression where

infixr 3 _⇨_
data Type : Set where
 int   : Type
 _⇨_   : Type → Type → Type

test : Type → Type
test int = int
test (φ ⇨ int) = test φ
test (φ ⇨ (φ′ ⇨ φ″))  = test (φ′ ⇨ φ″)
-- this should terminate since rec. call on subterm

test' : Type → Type
test' int = int
test' (φ ⇨ int) = test' φ
test' (φ ⇨ φ′)  = test' φ′

-- This no longer checks after the fix to issue 59, since the fact
-- that we case on φ′ in particular is lost.

-- ok : Type → Type
-- ok int = int
-- ok (φ ⇨ φ′) with φ′
-- ... | int = ok φ
-- ... | (φ″ ⇨ φ‴) = ok (φ″ ⇨ φ‴)
