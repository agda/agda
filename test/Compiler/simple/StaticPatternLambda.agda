
module _ where

open import Common.Prelude

case_of_ : {A B : Set} → A → (A → B) → B
case x of f = f x
{-# INLINE case_of_ #-}

patlam : Nat → Nat
patlam zero = zero
patlam (suc n) =
  case n of λ
  { zero    → zero
  ; (suc m) → m + patlam n
  }

static : {A : Set} → A → A
static x = x
{-# STATIC static #-}

-- The static here will make the compiler get to the pattern lambda in the body of patlam
-- before compiling patlam. If we're not careful this might make the pattern lambda not
-- inline in the body of patlam.
foo : Nat → Nat
foo n = static (patlam (suc n))

main : IO Unit
main = printNat (foo 5)
