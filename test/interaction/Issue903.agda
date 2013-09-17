-- This bug was reported by Christian Sattler. (I modified his example
-- slightly.)

-- {-# OPTIONS -v tc.meta.assign:49 #-}

module Issue903 where

record T : Set where
  constructor tt

postulate
  Id : (A : Set) → A → Set
  e  : (B : Set) (f : T → B) → Id B (f tt) → Id (T → B) f
  k  : (P : Set → Set) (u : P T) → Id (P T) u → T
  h  : Id T tt

q : T
q = k {!!} {!!} (e {!!} _ {!h!})

-- WAS: If one tries to give h:
--
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/MetaVars.hs:654
