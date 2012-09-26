-- 2012-09-25 Andreas, reported by Nicolas Pouillard
{-# OPTIONS --sized-types #-}
module Issue700 where

import Common.Level
open import Common.Size

postulate
  Size< : Size → Set
{-# BUILTIN SIZELT Size< #-}

postulate
  A : Set

data T (i : Size) : Set where
  c : (j : Size< i) → T j → T _

bug : ∀ i → T i → A
bug i (c j x) = bug j x

{- WAS: de Bruijn index out of scope

Issue700.bug is projection like in argument 1 for type Issue700.T
Translated clause:
  delta = (j : Size< @0) (x : T j)
  perm  = x0,x1 -> x0,x1
  ps    = [r(ConP Issue700.T.c Nothing [r(VarP "j"),r(VarP "x")])]
  body  = Bind (Abs "h1" Bind (Abs "h2" Body (Def Issue700.bug [r(Var 1 []),r(Var 0 [])])))
  body  = [h1 h2] bug h1 h2
-}
