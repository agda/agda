module TestQuote where

{- test of reflection, implementing a trivial prover. -}

data Bool : Set where
  true false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

postulate String : Set

{-# BUILTIN STRING String #-}

primitive
  primStringEquality : String → String → Bool

_==_ : String → String → Bool
_==_ = primStringEquality

data ⊥ : Set where
record ⊤ : Set where

data Thm : Set where
  triv : Thm

⟦_⟧ : String → Set
⟦ s ⟧ with s == "Thm"
...      | true = Thm
...      | false = ⊥

Hyp : String → Set → Set
Hyp s A with s == "Thm"
...      | true = ⊤
...      | false = A

solve : (s : String) → Hyp s ⟦ s ⟧ → ⟦ s ⟧ 
solve s h  with s == "Thm"
...      | true = triv
...      | false = h

test1 : Thm
test1 = quoteGoal t in (solve t _)

test2 : String
test2 = quote (λ (x : Set) → Set)
  