-- Andreas, 2017-09-09
-- Builtin constructors may be ambiguous / overloaded.

data Semmel : Set where
  false : Semmel

data Bool : Set where
  true  : Bool
  false : Bool

{-# BUILTIN BOOL  Bool #-}
{-# BUILTIN TRUE  true #-}
{-# BUILTIN FALSE false  #-}  -- This is accepted.

data Brezel (A : Set) : Set where
  _∷_ : (x : A) (xs : Brezel A) → Brezel A

data List₀ (A : Set) : Set where
  []  : List₀ A
  _∷_ : (x : A) (xs : List₀ A) → List₀ A

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List₀ #-}
