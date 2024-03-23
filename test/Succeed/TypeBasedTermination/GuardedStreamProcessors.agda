-- Tests stream processors complying with guardedness
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.GuardedStreamProcessors where

data Pair (A B : Set) : Set where
  pair : A → B → Pair A B

fst : {A B : Set} → (Pair A B) → A
fst (pair a _) = a

snd : {A B : Set} → Pair A B → B
snd (pair _ b) = b

record Stream' (A : Set) : Set where
  coinductive
  field
    force' : Pair A (Stream' A)

open Stream'

data SPμ (A B : Set) : Set
record SPν (A B : Set) : Set

data SPμ A B where
  get : (A → SPμ A B) → SPμ A B
  put : B → SPν A B → SPμ A B

record SPν A B where
  coinductive
  field
    force : SPμ A B

runSPμ' : {A B : Set} → SPμ A B → Stream' A → Pair B (Stream' B)
runSPν' : {A B : Set} → SPν A B → Stream' A → Stream' B

runSPμ' (put b spν) s = pair b (runSPν' spν s)
runSPμ' (get f) s = runSPμ' (f (fst (force' s))) (snd (force' s))
force' (runSPν' spn s) = runSPμ' (SPν.force spn) s
