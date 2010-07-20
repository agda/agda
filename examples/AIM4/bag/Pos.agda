
module Pos where

  import Prelude
  import Equiv
  import Datoid
  import Nat

  open Prelude
  open Equiv
  open Datoid

  abstract

    Pos : Set
    Pos = Nat.Nat

    one : Pos
    one = Nat.zero

    suc : Pos -> Pos
    suc = Nat.suc

    suc' : Nat.Nat -> Pos
    suc' n = n

    _+_ : Pos -> Pos -> Pos
    m + n = suc (Nat._+_ m n)

    -- Returns Nothing if input is 1.
    pred : Pos -> Maybe Pos
    pred Nat.zero    = Nothing
    pred (Nat.suc n) = Just n

    toNat : Pos -> Nat.Nat
    toNat = suc

    decidableEquiv : DecidableEquiv Pos
    decidableEquiv = Nat.decidableEquiv

  posDatoid : Datoid
  posDatoid = datoid Pos decidableEquiv

  sucPred : Maybe Pos -> Pos
  sucPred Nothing  = one
  sucPred (Just p) = suc p

  data Pred (p : Pos) (mP : Maybe Pos) : Set where
    ok : datoidRel posDatoid (sucPred mP) p -> Pred p mP

  abstract

    -- Returns Nothing if input is 1.
    predOK : (p : Pos) -> Pred p (pred p)
    predOK Nat.zero    = ok (dRefl posDatoid {one})
    predOK (Nat.suc n) = ok (dRefl posDatoid {n})
