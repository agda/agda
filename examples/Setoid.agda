
module examples.Setoid where

module Logic where

  infix 4 /\
  infix 2 \/
  infixr 1 -->

  data True : Prop where
    tt : True

  data False : Prop where

  data (/\) (P,Q:Prop) : Prop where
    andI : P -> Q -> P /\ Q

  data (\/) (P,Q:Prop) : Prop where
    orIL : P -> P \/ Q
    orIR : Q -> P \/ Q

  data (-->) (P,Q:Prop) : Prop where
    impI : (P -> Q) -> P --> Q

  impE : {P,Q:Prop} -> (P --> Q) -> P -> Q
  impE (impI h) = h

  data ForAll {A:Set}(P:A -> Prop) : Prop where
    forallI : ((x:A) -> P x) -> ForAll P

  forallE : {A:Set} -> {P:A -> Prop} -> ForAll P -> (x:A) -> P x
  forallE (forallI h) = h

module Setoid where

  data Setoid : Set1 where
    setoid : (A     : Set)
	  -> ((==)  : A -> A -> Prop)
	  -> (refl  : (x:A) -> x == x)
	  -> (sym   : (x,y:A) -> x == y -> y == x)
	  -> (trans : (x,y,z:A) -> x == y -> y == z -> x == z)
	  -> Setoid

  El : Setoid -> Set
  El (setoid A _ _ _ _) = A

  module Projections where

    eq : (A:Setoid) -> El A -> El A -> Prop
    eq (setoid _ eq _ _ _) = eq

    refl : (A:Setoid) -> {x:El A} -> eq A x x
    refl (setoid _ _ refl _ _) = refl _

    sym : (A:Setoid) -> {x,y:El A} -> eq A x y -> eq A y x
    sym (setoid _ _ _ sym _) = sym _ _

    trans : (A:Setoid) -> {x,y,z:El A} -> eq A x y -> eq A y z -> eq A x z
    trans (setoid _ _ _ _ trans) = trans _ _ _

  module Equality (A:Setoid) where

    infix 6 ==

    (==) : El A -> El A -> Prop
    (==) = Projections.eq A

    refl : {x:El A} -> x == x
    refl = Projections.refl A

    sym : {x,y:El A} -> x == y -> y == x
    sym = Projections.sym A

    trans : {x,y,z:El A} -> x == y -> y == z -> x == z
    trans = Projections.trans A

module Nat where

  open Logic
  open Setoid

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  NAT : Setoid
  NAT = setoid Nat eqNat r s t
    where
      eqNat : Nat -> Nat -> Prop
      eqNat zero     zero   = True
      eqNat zero    (suc _) = False
      eqNat (suc _)  zero   = False
      eqNat (suc n) (suc m) = eqNat n m

      r : (x:Nat) -> eqNat x x
      r zero	= tt
      r (suc n) = r n

      s : (x,y:Nat) -> eqNat x y -> eqNat y x
      s  zero    zero   _ = tt
      s (suc n) (suc m) h = s n m h

      t : (x,y,z:Nat) -> eqNat x y -> eqNat y z -> eqNat x z
      t  zero    zero    z      xy yz = yz
      t (suc x) (suc y) (suc z) xy yz = t x y z xy yz

module List where

  open Logic
  open Setoid

  data List (A:Set) : Set where
    nil  : List A
    (::) : A -> List A -> List A

  LIST : Setoid -> Setoid
  LIST A = setoid (List (El A)) eqList r s t
    where
      module EqA = Equality A
      open EqA

      eqList : List (El A) -> List (El A) -> Prop
      eqList nil      nil    = True
      eqList nil     (_::_)  = False
      eqList (_::_)   nil    = False
      eqList (x::xs) (y::ys) = x == y /\ eqList xs ys

      r : (x:List (El A)) -> eqList x x
      r  nil	= tt
      r (x::xs) = andI refl (r xs)

      s : (x,y:List (El A)) -> eqList x y -> eqList y x
      s  nil     nil     h            = h
      s (x::xs) (y::ys) (andI xy xys) = andI (sym xy) (s xs ys xys)

      t : (x,y,z:List (El A)) -> eqList x y -> eqList y z -> eqList x z
      t  nil     nil     zs      _             h            = h
      t (x::xs) (y::ys) (z::zs) (andI xy xys) (andI yz yzs) =
        andI (trans xy yz) (t xs ys zs xys yzs)

module Fun where

  open Logic
  open Setoid

  infixr 10 =>

  data (=>) (A,B:Set) : Set where
    lam : (A -> B) -> A => B

  app : {A,B:Set} -> (A => B) -> A -> B
  app (lam f) = f

  (==>) : Setoid -> Setoid -> Setoid
  A ==> B = setoid FunAB eqFun ? ? ?
    where
      module EqA = Equality A
      module EqB = Equality B

      postulate FunAB : Set
		eqFun : FunAB -> FunAB -> Prop

      -- FunAB won't fit in Set!
--       data FunAB : Set where
-- 	lam' : (f    : El A => El B)
-- 	    -> (resp : (x,y : El A) -> EqA.== x y --> EqB.== (app f x) (app f y))
-- 	    -> FunAB
-- 
--       app' : FunAB -> El A => El B
--       app' (lam' f _) = f
-- 
--       eqFun : FunAB -> FunAB -> Prop
--       eqFun f g =
-- 	ForAll (\x -> ForAll (\y ->
-- 		  EqA.== x y -->
-- 		  EqB.== (f `app'` x) (g `app'` y)
-- 	       ))
-- 
--       r : (f : El A => El B) -> eqFun f f
--       r (lam f) = forallI (\x -> EqB.refl)
-- 
