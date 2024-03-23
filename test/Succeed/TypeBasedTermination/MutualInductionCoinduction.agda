-- Tests a mix of inductive and coinductive matchings in a function
{-# OPTIONS --type-based-termination --no-syntax-based-termination #-}

module TypeBasedTermination.MutualInductionCoinduction where

record Stream (A : Set) : Set where
  constructor _,_
  coinductive
  field
    hd : A
    tl : Stream A

open Stream

data   SPμ (A B : Set) : Set
record SPν (A B : Set) : Set

data SPμ A B where
  get : (A → SPμ A B) → SPμ A B
  put : B → SPν A B → SPμ A B

record SPν A B where
  coinductive
  field
    force : SPμ A B

open SPν

runSPμ : {A B : Set} → SPμ A B → Stream A → Stream B

runSPμ (put b spν) s .hd = b
runSPμ (put b spν) s .tl = runSPμ (SPν.force spν) s
runSPμ (get f) s = runSPμ (f (s .hd)) (s .tl)

runSPν : {A B : Set} → SPν A B → Stream A → Stream B
runSPν spν s = runSPμ (SPν.force spν) s

idSP : {A : Set} → SPν A A
idSP .force = get (λ a → get (λ a' → put a idSP))
