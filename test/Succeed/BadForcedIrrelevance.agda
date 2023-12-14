{-# OPTIONS --erasure #-}

open import Agda.Builtin.Nat

data V : (n : Nat) → Set where
  cons : (n : Nat) → V (suc n)
       -- ^ this n is forced

    -- v and this n is marked erased
g : (@erased n : Nat) → V n → Nat
g _ (cons n) = n
--             ^ so we can't return n here, since we're really
--               returning the erased one.

-- Jesper, 2023-09-20 (#6867): Now we no longer mark `n` as forced, so this
-- example is accepted.
