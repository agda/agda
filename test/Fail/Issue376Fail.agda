

import Common.Level
open import Common.Equality

record Sigma (A : Set)(B : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst
open Sigma

-- projected bound var
fail : (A : Set) (B : A -> Set) ->
  let X : A -> Sigma A B
      X = _
  in  (z : Sigma A B) -> X (fst z) ≡ z
fail A B z = refl
