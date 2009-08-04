module Homogenous.Reflexivity where
import Homogenous.Base
import Homogenous.Equality
open Homogenous.Base     using(Arity; Sig; Fa; Fa1; F; F1; T; It; FIHa; FIH; R)
open Homogenous.Equality using(equal; eq_step; eq_step'; eq_step_ar)

import PolyDepPrelude
open PolyDepPrelude using(Bool; true; false; True;
                   pair; fst; snd;
                   zero; suc;
                   left; right;
                   _::_; nil;
                   unit)
import Tools
open Tools       using(liftAnd)
import Reflexivity
open Reflexivity using(lref; Refl; refl)

-- -----------------------------
-- Reflexivity

-- Short-hand notation for mapping a rel. over Fa resp. F

Fa1rel : (n : Arity)-> (X : Set) -> (X -> X -> Bool) ->
         Fa n X -> Fa n (X -> Bool)
Fa1rel n X r = Fa1 n (\x -> (\y -> r x y) )

F1rel  : (fi : Sig)(X : Set) -> (X -> X -> Bool) -> F fi X -> F fi (X -> Bool)
F1rel fi X r = F1 fi (\x -> (\y -> r x y) )

-- Now the real reflexivity lemmas start

ref_eq_step_ar : (n : Arity) (Y : Set) (e : Y -> Y -> Bool) (x : Fa n Y)
                 (ih : FIHa n (lref e) x)
  -> True (eq_step_ar n (Fa1rel n Y e x) x)
ref_eq_step_ar (zero)  Y e (unit)      (unit)      = unit
ref_eq_step_ar (suc m) Y e (pair y ys) (pair r rs) with e y y | r
ref_eq_step_ar (suc m) Y e (pair y ys) (pair r rs) | false | ()
ref_eq_step_ar (suc m) Y e (pair y ys) (pair r rs) | true  | unit =
  ref_eq_step_ar m Y e ys rs

-- Reflexivity for matching constructors is trivial
ref_eq_step' : (fi : Sig)(X : Set)(e : X -> X -> Bool)(x : F fi X)
  -> FIH fi (lref e) x -> True (eq_step' fi (F1rel fi X e x) x)
ref_eq_step' (nil)   X e () -- empty
ref_eq_step' (n :: ns) X e (left  x') = ref_eq_step_ar n X e x'
ref_eq_step' (n :: ns) X e (right y)  = ref_eq_step'  ns X e y

ref_eq' : (fi : Sig) -> (x : T fi) -> lref (equal fi) x
ref_eq' fi =      R fi (ref_eq_step' fi (T fi) (equal fi))

ref_eq : (fi : Sig) -> Refl (equal fi)
ref_eq fi = refl (R fi (ref_eq_step' fi (T fi) (equal fi)))
