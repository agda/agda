module Issue246 where

module James where

  data Nat : Set where
    zero  : Nat
    suc   : Nat -> Nat

  data Zero : Set where

  data One : Set where
    void : One

  propLEQ : Nat -> Nat -> Set
  propLEQ zero    _       = One
  propLEQ (suc n) (suc m) = propLEQ n m
  propLEQ (suc n) zero    = Zero

  data Fin : Nat -> Set where
    fzero : {n : Nat} -> Fin (suc n)
    fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

  toFin : {n : Nat} -> (i : Nat) -> (propLEQ (suc i) n) -> Fin n
  toFin {zero}  zero      ()
  toFin {zero}  (suc _)   ()
  toFin {suc n} zero    k  = fzero
  toFin {suc n} (suc i) k  = fsuc (toFin i k)

  one : Nat
  one = suc zero

  two : Nat
  two = suc one

  three : Nat
  three = suc two

  null : Fin three
  null = toFin zero void

module Conor where

  data Nat : Set where
   ze : Nat
   su : Nat -> Nat

  data Bool : Set where
   tt ff : Bool

  record One : Set where
  data Zero : Set where

  So : Bool -> Set
  So tt = One
  So ff = Zero

  _<_ : Nat -> Nat -> Bool
  _ < ze = ff
  ze < su n = tt
  su m < su n = m < n

  data Lt (m n : Nat) : Set where
   lt : So (m < n) -> Lt m n

  boo : {m n : Nat} -> So (m < n) -> Lt (su m) (su n)
  boo p = lt p

module Alan where

  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

  {-# BUILTIN NATURAL ℕ #-}
  {-# BUILTIN ZERO zero #-}
  {-# BUILTIN SUC suc #-}

  data Bool : Set where
    true false : Bool

  infixr 5 _∷_

  _lt_ : ℕ → ℕ → Bool
  _     lt zero  = false
  zero  lt suc _ = true
  suc x lt suc y = x lt y

  data List<? (X : ℕ → Set) (n : ℕ) : Bool → Set where
    [] : List<? X n true
    _∷_ : {m : ℕ} → (x : X m) → (List<? X m true) → (List<? X n (m lt n))

  List< : (ℕ → Set) → ℕ → Set
  List< X n = List<? X n true

  data A : ℕ → Set where
    a1 : A 1
    a2 : A 2

  as : List< A 3
  as = a2 ∷ a1 ∷ ([] {A})

  as' : List< A 3
  as' = a2 ∷ a1 ∷ []
