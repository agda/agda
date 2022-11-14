{-# OPTIONS --no-load-primitives #-}

-- Andreas, 2022-10-06, PR #6161:
-- Also test --no-load-primitives.

{-# BUILTIN TYPE Type #-}
{-# BUILTIN PROP Prop #-}
{-# BUILTIN SETOMEGA Typeω #-}
{-# BUILTIN STRICTSET SSet #-}
{-# BUILTIN STRICTSETOMEGA SSetω #-}

postulate
  Level : Type
  lzero : Level
  lsuc  : Level → Level
  _⊔_   : Level → Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC lsuc #-}
{-# BUILTIN LEVELMAX _⊔_ #-}

-- We cannot import the builtin modules since they use Agda.Primitive.

postulate IO : ∀ {a} → Type a → Type a

{-# BUILTIN IO IO #-}
{-# FOREIGN GHC type AgdaIO a b = IO b #-}
{-# COMPILE GHC IO = type AgdaIO #-}

data Nat : Type where
  zero : Nat
  suc  : (n : Nat) → Nat

{-# BUILTIN NATURAL Nat #-}

record ⊤ : Type where

{-# BUILTIN UNIT ⊤ #-}
{-# COMPILE GHC ⊤ = data () (()) #-}

private
  n : Nat
  n = 7

{-# COMPILE GHC n as n #-}

postulate
  main : IO ⊤

{-# COMPILE GHC main = print n #-}
