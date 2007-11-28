{-# OPTIONS --no-positivity-check --no-termination-check #-}
module Homogenous.Base where
-- module Homogenous.Base(Arity, Sig, T, Intro) where

import TYPE
import PolyDepPrelude

open PolyDepPrelude using
  ( Absurd
  ; Unit; unit
  ; Nat; zero; suc
  ; List; nil; _::_
  ; Either; left; right
  ; Pair; pair)

-- A homogenous algebra can be represented by a list of arities
--   (natural numbers)

Arity : Set
Arity = Nat

Sig   : Set
Sig   = List Arity

-- Many definitions below come in pairs - one for Arity and one for
-- Sig - where name of the first one ends in a (as in Arity) :
--   funa : Arity -> ...
--   fun  : Sig -> ...

-- (Fa n,Fa1 n) is the functor "n-tuple of same type" or
--                 "vector of length n" or "(^n)"

Fa : (n : Arity) -> Set -> Set
Fa (zero)  X = Unit
Fa (suc m) X = Pair X (Fa m X)

 ----------------------------------------------------------------
Fa1 : (n : Arity) -> {a b : Set} -> (a -> b) -> Fa n a -> Fa n b
Fa1 (zero)  f (unit)         = unit
Fa1 (suc m) f (pair fst snd) = pair (f fst) (Fa1 m f snd)

-- (F fi, F1 fi) is the pattern functor for a homogenous algebra

F : (fi : Sig)(X : Set) -> Set
F (nil)      X = Absurd
F (n :: fi') X = Either (Fa n X) (F fi' X)

F1 : (fi : Sig){a b : Set}(f : a -> b)(x : F fi a) -> F fi b
F1 (nil)      f ()        -- empty
F1 (n :: ns)  f (left  t) = left  (Fa1 n f t)
F1 (n :: ns)  f (right y) = right (F1 ns f y)

-- For the definition of the recursor R we need family-level
-- variants of F and F1 : FIH and Fmap. As usual we define these first
-- for arities (with a postfix 'a' in the name) and then for signatures.

FIHa : (n : Arity){X : Set}(C : X -> Set)(x : Fa n X) -> Set
FIHa (zero)  C unit           = Unit
FIHa (suc m) C (pair fst snd) = Pair (C fst) (FIHa m C snd)

FIH : (fi : Sig){X : Set}(C : X -> Set)(x : F fi X) -> Set
FIH (nil)      C ()      -- empty
FIH (n :: ns)  C (left  t) = FIHa n C t
FIH (n :: ns)  C (right y) = FIH ns C y

Fmapa : (n : Arity){X : Set}{C : X -> Set}(h : (x : X) -> C x)(u : Fa n X)
      -> FIHa n C u
Fmapa (zero)  h (unit)         = unit
Fmapa (suc m) h (pair fst snd) = pair (h fst) (Fmapa m h snd)

Fmap : (fi : Sig){X : Set}{C : X -> Set}(h : (x : X) -> C x)(u : F fi X)
     -> FIH fi C u
Fmap (nil)      h () -- empty
Fmap (n :: ns)  h (left  x) = Fmapa n h x
Fmap (n :: ns)  h (right y) = Fmap ns h y

-- Finally the homogenous algebra construction itself - for each code
-- fi there is a datatype T fi and an iterator It fi

data T (fi : Sig) : Set where
  Intro : F fi (T fi) -> T fi

It : (fi : Sig){C : Set}(d : F fi C -> C) -> T fi -> C
It fi d (Intro i) = d (F1 fi (It fi d) i)

-- Mendler style iterator is also straight forward

MIt : (fi : Sig){C : Set}(s : {X : Set} -> (X -> C) -> F fi X -> C)
    -> T fi -> C
MIt fi s (Intro i) = s (MIt fi s) i

R : (fi : Sig)
    {C : T fi -> Set}
    (d : (y : F fi (T fi)) -> FIH fi C y -> C (Intro y))
    (x : T fi) -> C x
R fi d (Intro i) = d i (Fmap fi (R fi d) i)

-- Special case of FIH

FIHs : (fi : Sig) -> (T fi -> Set) -> F fi (T fi) -> Set
FIHs fi = FIH fi

-- A simple example : the inverse of Intro

out : (fi : Sig) -> T fi -> F fi (T fi)
out fi = R fi (\y p -> y)

----------------------------------------------------------------
-- Now for the Type level : define FIHa, FIH, Fmapa, Fmap again
--   (universe polymorphism, please!)

FIHaT : (n : Arity)(X : Set)(C : X -> Set1)(x : Fa n X) -> Set1
FIHaT (zero)  X C (unit)         = TYPE.Unit
FIHaT (suc m) X C (pair fst snd) = TYPE.Pair (C fst) (FIHaT m X C snd)


FIHT : (fi : Sig)(X : Set)(C : X -> Set1)(x : F fi X) -> Set1
FIHT (nil)      X C () -- empty
FIHT (n :: ns)  X C (left  t) = FIHaT n X C t
FIHT (n :: ns)  X C (right y) = FIHT ns X C y

FIHsT : (fi : Sig)(C : T fi -> Set1)(x : F fi (T fi)) -> Set1
FIHsT fi C x = FIHT fi (T fi) C x

FmapaT : (n : Arity){X : Set}{C : X -> Set1}(h : (x : X) -> C x)(u : Fa n X)
  -> FIHaT n X C u
FmapaT (zero)  h (unit)         = TYPE.unit
FmapaT (suc m) h (pair fst snd) = TYPE.pair (h fst) (FmapaT m h snd)

FmapT : (fi : Sig){X : Set}{C : X -> Set1}(h : (x : X) -> C x)(u : F fi X)
      -> FIHT fi X C u
FmapT (nil)      h () -- empty
FmapT (n :: ns)  h (left  x') = FmapaT n h x'
FmapT (n :: ns)  h (right y)  = FmapT ns h y

RT : (fi : Sig)
     {C : T fi -> Set1}
     (d : (y : F fi (T fi)) -> FIHT fi (T fi) C y -> C (Intro y))
     (x : T fi) -> C x
RT fi d (Intro i) = d i (FmapT fi (RT fi d) i)
