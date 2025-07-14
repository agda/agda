-- Andreas, 2025-07-14, issue #7998
-- Instance keywords in primitive blocks should not be silently ignored.

module _ where

primitive
  instance -- UselessInstance
    primLockUniv : Set₁

-- Expect warning about useless "instance".

open import Agda.Builtin.Nat

postulate
  private
    Word64 : Set

{-# BUILTIN WORD64 Word64 #-}

-- Can have private block in primitive block.

instance  -- UselessInstance
  primitive
    private
      primWord64ToNat : Word64 → Nat

-- Expect warning about useless "instance", though.

primitive  -- EmptyPrimitive

primitive  -- EmptyPrimitive
  private  -- UselessPrivate

postulate  -- EmptyPostulate
  private  -- UselessPrivate

private         -- UselessPrivate
  data _ where  -- EmptyConstructor

data _ where    -- EmptyConstructor
  instance      -- UselessInstance

module M where
  interleaved mutual
    data D : Set
    private         -- Expected UselessPrivate
      data _ where
        c : D

d : M.D
d = M.c
