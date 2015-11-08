{-# OPTIONS --type-in-type #-}

module NoUniverseCheck where

data M : Set -> Set where
  return : forall {a}   -> a -> M a
  _>>=_  : forall {a b} -> M a -> (a -> M b) -> M b

record Cat : Set where
  field
    Obj : Set
    Mor : Obj -> Obj -> Set

data _≡_ {a : Set} (x : a) : a -> Set where
  refl : x ≡ x

CatOfCat : Cat
CatOfCat = record
  { Obj = Cat
  ; Mor = _≡_
  }
