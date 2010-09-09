
module Agda.TypeChecking.RecordPatterns where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

{- How to translate a clause with patterns into one that does irrefutable
   matching on records

f (zero, (x, (y, z))) true (x', false) = rhs

 translates to

f (zero, xyz) true (x', false) rhs'  where rhs = subst
  [ fst xyz       / x, 
    fst (snd xyz) / y,
    snd (snd xyz) / z,
    x' / x'
  ] rhs'

We walk through the patterns from left to right, to get the de Bruijn indices
for the pattern variables (dot patterns also have a de Bruijn index).

If we return from a record pattern whose components were all irrefutable, we
apply a substitution to Telescope

-}

translateRecordPatterns :: MonadTCM tcm => Clause -> tcm Clause
translateRecordPatterns clause = return clause
