{-# OPTIONS --copatterns --allow-unsolved-metas #-}

module Issue942  where

record Sigma (A : Set)(P : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : P fst
open Sigma

postulate
  A : Set
  x : A
  P Q : A → Set
  Px : P x
  f  : ∀ {x} → P x → Q x

ex : Sigma A Q
ex = record
       { fst = x
       ; snd = f {!!} -- goal: P x
       }

ex' : Sigma A Q
ex' = x , f {!!} -- goal: P x

ex'' : Sigma A Q
fst ex'' = x
snd ex'' = f {!!} -- goal: P (fst ex'')

-- should termination check
