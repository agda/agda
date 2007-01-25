module Homogenous.Reflexivity where
import Homogenous.Base
import Homogenous.Equality
open Homogenous.Base	 using(Arity; Sig; Fa; Fa1; F; F1; T; It; FIHa; FIH; R)
open Homogenous.Equality using(equal; eq_step; eq_step'; eq_step_ar)

import Prelude
open Prelude using(Bool; True;
                    pair; fst; snd;
                    zero; suc;
                    left; right;
                    _::_; nil;
                    _=>_; lam; _$$_;
                    unit)
import Tools
open Tools       using(liftAnd)
import Reflexivity
open Reflexivity using(lref; Refl; refl)

-- -----------------------------
-- Reflexivity

-- Short-hand notation for mapping a rel. over Fa resp. F

Fa1rel : (n:Arity)-> (X:Set) -> (X -> X -> Bool) -> Fa n X -> Fa n (X => Bool)
Fa1rel n X r = Fa1 n (\x -> lam (\y -> r x y) )

F1rel  : (fi:Sig)(X:Set) -> (X -> X -> Bool) -> F fi X -> F fi (X => Bool)
F1rel fi X r = F1 fi (\x -> lam (\y -> r x y) )

-- Now the real reflexivity lemmas start

ref_eq_step_ar : (n:Arity) (Y:Set) (e:Y -> Y -> Bool) (x:Fa n Y)
                 (ih:FIHa n (lref e) x)
  -> True (eq_step_ar n (Fa1rel n Y e x) x)
ref_eq_step_ar   (zero)  Y e   (unit)      (unit)      = unit
ref_eq_step_ar   (suc m) Y e   (pair y ys) (pair r rs) = unit

-- Reflexivity for matching constructors is trivial
ref_eq_step' : (fi:Sig)(X:Set)(e:X -> X -> Bool)(x:F fi X)
  -> FIH fi (lref e) x -> True (eq_step' fi (F1rel fi X e x) x)
ref_eq_step' (nil)   X e () -- empty
ref_eq_step' (n::ns) X e (left  x') = ref_eq_step_ar n X e x'
ref_eq_step' (n::ns) X e (right y)  = ref_eq_step'  ns X e y

ref_eq' : (fi:Sig) -> (x: T fi) -> lref (equal fi) x
ref_eq' fi = R fi (ref_eq_step' fi (T fi) {!equal fi!})


ref_eq : (fi:Sig) -> Refl (equal fi)
ref_eq fi = refl (R fi (ref_eq_step' {!!}
                                     (T fi)
                                     {!!}))




{-

R : (fi:Sig)
    {C:T fi -> Set}
    (d:(y:F fi (T fi)) -> FIH fi C y -> C (Intro y))
    (x:T fi) -> C x

(y:F fi (T fi)) -> FIH fi C        y -> C (Intro y)
(y:F fi (T fi)) -> FIH fi (lref e) y -> True (eq_step' fi (F1rel fi (T fi) e y) y)

e           := equal fi
C           := lref e
C (Intro y) := True (eq_step' fi (F1rel fi (T fi) e y) y)
               True (eq_step' fi (F1 fi (\x -> lam (\y -> e x y)) y) y)
               True (eq_step' fi (F1 fi (\x -> lam (\y -> equal fi x y)) y) y)
               True (eq_step' fi (F1 fi (\x -> lam (\y -> equal' fi x $$ y)) y) y)
LHS =          True (eq_step' fi (F1 fi (equal' fi              ) y) y)


The gap is

  \x -> lam (\y -> q x $$ y) === q     : A -> B => C


  lref e (Intro y)
==
  True (e (Intro y) (Intro y))
==
  True (equal fi (Intro y) (Intro y))
==
  True (equal' fi (Intro y) $$ (Intro y))
==
  True (It fi (eq_step fi) (Intro y) $$ (Intro y))
==
  True (eq_step fi (F1 fi (It fi (eq_step fi)) y)   $$ (Intro y))
==
  True (lam ( \t -> eq_step' fi (F1 fi (It fi (eq_step fi)) y) (out fi t) )
        $$  (Intro y))
==
  True (eq_step' fi (F1 fi (It fi (eq_step fi)) y) (out fi (Intro y)) )
==
  True (eq_step' fi (F1 fi (It fi (eq_step fi)) y) y)
==
  True (eq_step' fi (F1 fi (It fi (eq_step fi)) y) y)

-}


{-
  ref_eq_step : (fi:Sig)(e:rel (T fi))
    -> (x:F fi (T fi)) ->
       FIH fi (T fi) (lref (T fi) e) x ->
       True (eq_step fi (F1rel fi (T fi) e x) (Intro x))
   ref_eq_step fi w = ref_eq_step' fi (T fi) e

  ref_eq : (fi:Sig) -> Refl (T fi) (equal fi)
  ref_eq fi = R fi (lref (T fi) (equal fi)) (ref_eq_step fi (equal fi))
-}

{-
module Homogenous_Reflexivity_zip where

  open Homogenous_Base     use Arity, Sig, Fa, Fa1, F, F1, T, It, FIHa, FIH, R
  open Homogenous_Equality_zip use equal, eq_step, recogAll,  Eq,
                                      andA, zipWithA, zipWithApply,
                                      andzipWithA, matchAndZipWith,
                                      andzipWithApply, match, match2
  open Tools  use  liftAnd
  open Reflexivity use lref, Refl


  -- Preliminaries (lemmas)

  -- F1 distributes over matchAndZipWith

  convertA (n:Arity)(X:Set)(e:Eq X X)(x:Fa n X)(P:Bool->Set)
    (p:P (andzipWithA X X e n x x)) :
    P (andzipWithA (X->Bool) X id n (Fa1 n e x) x)
    = case n of
      (zero )-> case x of (tt)-> p
      (suc m)-> convertA m X e x.snd (\(b:Bool)-> P (and (e x.fst x.fst) b)) p

  convertS (fi:Sig)(X:Set)(e:Eq X X)(x:F fi X)(P:Bool->Set)
    (p:P (matchAndZipWith X X e fi x x)) :
    P (matchAndZipWith (X->Bool) X id fi (F1 fi e x) x)
    = case fi of
      (nil     )-> case x of { }
      (con n ns)-> case x of
                    (left  xl)-> convertA n X e xl P p
                    (right xr)-> convertS ns X e xr P p

  -- Reflexivity for the Arity level

  ref_andzipWithA (n:Arity)(X:Set)(e:Eq X X)(x:Fa n X)
       (xs:FIHa n X (lref X e) x)
    : lref (Fa n X) (andzipWithA X X e n) x
    = case n of
      (zero )-> case x of (tt)-> tt@_
      (suc m)-> liftAnd (e x.fst x.fst) (andzipWithA  X X e m x.snd x.snd)
                          xs.fst        (ref_andzipWithA m X e x.snd xs.snd)

  -- Reflexivity for the Sig level

  ref_match (fi:Sig)(X:Set)(e:Eq X X)(x:F fi X)
    : FIH fi X (lref X e) x ->
       lref (F fi X) (matchAndZipWith X X e fi) x
    = case fi of
      (nil     )-> case x of { }
      (con n ns)-> case x of (left  xl)-> ref_andzipWithA n X e xl
                             (right xr)-> ref_match ns X e xr
  --       True (matchAndZipWith X X e fi x x)

  -- ref_eq_step and ref_match have isomorphic types - convertS is
  -- used to convince Agda about this fact.
  -- The occurrance of F1 comes from the definition of It(eraror)

  ref_eq_step (fi:Sig)(X:Set)(e:Eq X X)(x:F fi X)
    : FIH fi X (lref X e) x ->
       True (recogAll X fi (F1 fi e x) x)
    = convertS fi X e x (\(b:Bool) -> FIH fi X (lref X e) x -> True b)
        (ref_match fi X e x)

  -- The top level proof uses the recursor R

  ref_eq (fi:Sig) : Refl (T fi) (equal fi)
     = R fi (ref_eq_step fi (T fi) (equal fi))

  -- Unused code:

  convertS' (fi:Sig)(X:Set)(e:Eq X X)(x:F fi X)(P:Bool->Set)
    (p:P (match X X (andzipWithA X X e) fi x x)) :
     P (match (X->Bool) X
           (andzipWithA (X->Bool) X id)
           fi
           (F1 fi e x)
           x
      )
    = case fi of
      (nil     )-> case x of { }
      (con n ns)-> case x of
                    (left  xl)-> convertA n X e xl P p
                    (right xr)-> convertS' ns X e xr P p

-}
