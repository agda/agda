-- Testing parameterised records in parameterised modules
module Exist (X : Set) where

data [_] (a : Set) : Set where
  []  : [ a ]
  _∷_ : a -> [ a ] -> [ a ]

map : forall {a b} -> (a -> b) -> [ a ] -> [ b ]
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

record ∃ (a : Set) (P : a -> Set) : Set where
  field
    witness : a
    proof   : P witness

ListP : (a : Set) -> (a -> Set) -> Set
ListP a P = [ ∃ a P ]

mapP : forall {a b P Q}
  -> (f : a -> b) -> (forall {x} -> P x -> Q (f x))
  -> ListP a P -> ListP b Q
mapP {a} {b} {P} {Q} f pres xs = map helper xs
  where
  helper : ∃ a P -> ∃ b Q
  helper r = record { witness = f (∃.witness r)
                    ; proof   = pres (∃.proof r)
                    }

