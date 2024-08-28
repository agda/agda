
module Issue756a where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data T : Nat → Set where
  [_] : ∀ n → T n

bad : ∀ n → T n → Nat
bad .zero                   [ zero  ] = zero
bad .(suc (let x = n in x)) [ suc n ] = zero

-- Expected error:
-- Let-expressions are not allowed in dot patterns
