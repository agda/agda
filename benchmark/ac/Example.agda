
module Example where

open import Bool
open import Nat hiding (_==_; _+_)
open import AC

open Provable

infix 40 _+_
infix 30 _==_

postulate
  X : Set
  _==_ : X -> X -> Set
  |0|  : X
  _+_  : X -> X -> X
  refl  : forall {x}     -> x == x
  sym   : forall {x y}   -> x == y -> y == x
  trans : forall {x y z} -> x == y -> y == z -> x == z
  idL   : forall {x}     -> |0| + x == x
  idR   : forall {x}     -> x + |0| == x
  comm  : forall {x y}   -> x + y == y + x
  assoc : forall {x y z} -> x + (y + z) == (x + y) + z
  congL : forall {x y z} -> y == z -> x + y == x + z
  congR : forall {x y z} -> x == y -> x + z == y + z

open Semantics
      _==_ _+_ |0| refl sym trans idL idR
      comm assoc congL congR

thm = theorem 11 \a b c d e f g h i j k ->
      j ○ (k ○ (((((h ○ (e ○ ((e ○ (a ○ (a ○ (b ○ ((c ○ (((c ○ (d ○ d)) ○ (((d
      ○ (d ○ ((d ○ ((e ○ k) ○ ((((a ○ b) ○ (((h ○ (k ○ f)) ○ (((d ○ ((j ○ (h ○
      (a ○ (((g ○ (k ○ g)) ○ ((b ○ (i ○ (i ○ ((i ○ ((k ○ (d ○ (b ○ ((b ○ ((h ○
      k) ○ e)) ○ a)))) ○ j)) ○ a)))) ○ i)) ○ h)))) ○ (g ○ h))) ○ f) ○ h)) ○ b))
      ○ f) ○ f))) ○ (e ○ d)))) ○ d) ○ c)) ○ c)) ○ b))))) ○ (((a ○ a) ○ k) ○
      e)))) ○ c) ○ h) ○ (d ○ a)) ○ (c ○ a)))
      ≡
      (j ○ (k ○ (((h ○ (h ○ e)) ○ ((((e ○ (((a ○ (b ○ ((b ○ c) ○ (((d ○ d) ○
      ((d ○ d) ○ ((((e ○ (e ○ (f ○ f))) ○ (((a ○ ((b ○ (h ○ (k ○ (h ○ ((f ○ ((h
      ○ ((h ○ (a ○ ((k ○ (g ○ (b ○ (k ○ ((((a ○ (((e ○ h) ○ k) ○ b)) ○ b) ○ d)
      ○ j))))) ○ ((((a ○ i) ○ i) ○ i) ○ i)))) ○ ((g ○ h) ○ g))) ○ (j ○ d))) ○
      f))))) ○ b)) ○ k) ○ d)) ○ d) ○ d))) ○ ((c ○ c) ○ c))))) ○ (a ○ a)) ○ a))
      ○ (k ○ e)) ○ c) ○ d)) ○ a))) ○ (c ○ a)

test = prove thm


