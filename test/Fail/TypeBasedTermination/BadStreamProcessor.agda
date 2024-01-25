-- Tests bad stream processors functions
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}
module TypeBasedTermination.BadStreamProcessor where

record Stream (A : Set) : Set where
  constructor _,_
  coinductive
  field
    hd : A
    tl : Stream A

open Stream

data SPμ (A B : Set) : Set
record SPν (A B : Set) : Set

data SPμ A B where
  get : (A → SPμ A B) → SPμ A B
  put : B → SPν A B → SPμ A B

record SPν A B where
  coinductive
  field
    force : SPμ A B

runSPμ : {A B : Set} → SPμ A B → Stream A → Stream B
runSPν : {A B : Set} → SPν A B → Stream A → Stream B

runSPμ (get f) s = runSPμ (f (hd s)) (tl s)
runSPμ (put b spν) s = (b , runSPν spν s)

runSPν spn s = runSPμ (SPν.force spn) s -- there is no size variable to be passed to SPν.force
