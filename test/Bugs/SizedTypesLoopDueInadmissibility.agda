{-# OPTIONS --sized-types #-}

module SizedTypesLoopDueInadmissibility where

open import Agda.Builtin.Size renaming (↑_ to _^)

data Nat : {size : Size} -> Set where
  zero : {size : Size} -> Nat {size ^}
  suc  : {size : Size} -> Nat {size} -> Nat {size ^}

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A -> Maybe A

shift_case : {i : Size} -> Maybe (Nat {i ^}) -> Maybe (Nat {i})
shift_case nothing = nothing
shift_case (just zero) = nothing
shift_case (just (suc x)) = just x

shift  : {i : Size} -> (Nat -> Maybe (Nat {i ^})) ->
                       (Nat -> Maybe (Nat {i}))
shift f n = shift_case (f (suc n))

inc : Nat -> Maybe Nat
inc n = just (suc n)

-- the type of the following recursive function should be rejected!!
-- it is inadmissible (see Abel, RAIRO 2004 or CSL 2006)
loop : {i : Size} -> Nat {i} -> (Nat -> Maybe (Nat {i})) -> Set
loop (suc n) f = loop n (shift f)
loop zero f with (f zero)
... | nothing = Nat
... | (just zero) = Nat
... | (just (suc y)) = loop y (shift f)

{-
mutual

  loop : {i : Size} -> Nat {i} -> (Nat -> Maybe (Nat {i})) -> Set
  loop .{i ^} (suc {i} n) f = loop {i} n (shift {i} f)
  loop .{i ^} (zero {i}) f = loop_case {i ^} (f zero) f

  loop_case : {i : Size} -> Maybe (Nat {i}) -> (Nat -> Maybe (Nat {i})) -> Set
  loop_case nothing f = Nat
  loop_case (just zero) f = Nat
  loop_case (just (suc y)) f = loop y (shift f)
-}

diverge = loop zero inc
