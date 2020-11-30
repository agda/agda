{-# OPTIONS --cumulativity #-}

open import Agda.Primitive

record Container a : Set (lsuc a) where
  constructor _◁_
  field
    Shape : Set a
    Pos   : Shape → Set a
open Container public

data Free {a : Level} (C : Container a) (A : Set a) : Set a where
  pure : A                                      → Free C A
  impure : (s : Shape C) → (Pos C s → Free C A) → Free C A

ROp : ∀ a → Container (lsuc a)
ROp a = Set a ◁ λ x → x

rop : {a : Level} {A : Set a} → Free (ROp a) A
rop {_} {A} = impure A pure

rop′ : {a : Level} {A : Set (lsuc a)} → Free (ROp a) A
rop′ {a} {A} = rop {a} -- This should not work, A : Set (suc a) is too large.
                       -- Passing it as an implicit parameter {A} gives the expected error.
