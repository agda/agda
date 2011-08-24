-- Modified: Andreas, 2011-04-11 freezing metas, removed unused uni.poly

{-# OPTIONS --guardedness-preserving-type-constructors #-}

module UnusedArgsInPositivity where

open import Common.Coinduction

module Ex₁ where
  data Unit : Set where
    unit : Unit

  unused : Set → Unit → Set → Set
  unused X unit Y = Y

  mutual

    data D : Set where
      d : (x : Unit) → (El x x → D) → D

    El : Unit → Unit → Set
    El unit x = unused D x Unit

module Ex₂ where

  data Maybe (A : Set) : Set where

  data Rec (A : ∞ Set) : Set where
    fold : ♭ A → Rec A

  mutual

    data Data : Set where
      maybe : ∞ Data -> Data
      sigma : (A : Data) → (El A → Data) -> Data

    El : Data → Set
    El (maybe A) = Rec (♯ Maybe (El (♭ {A = Data} A)))
    El (sigma A B) = El A

  {- This fails for 2 reasons:
     1. Rec doesn't preserve guardedness (hence -no-termination-check)
     2. Data "appears" in the definition of El
  The 1st one is now fixed.
  It is not clear how to fix the 2nd. Irrelevant parameters?
  -}

{-
/Users/txa/current/AIMXI/DataGuard.agda:15,8-12
Data is not strictly positive, because it occurs in the type of the
constructor sigma in the definition of Data, which occurs in the
second argument to ♭ in the first argument to El in the second
argument to Maybe in the first clause in the definition of
.DataGuard.♯-0, which occurs in the third clause in the definition
of El.
-}

module Ex₃ where
  data D (A : Set) : Set where
    d : D A

  data E : Set where
    e : (D E → E) → E
