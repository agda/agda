module Setoid where

module Logic where

  infix 4 _/\_
  -- infix 2 _\/_

  data True : Set where
    tt : True

  data False : Set where

  data _/\_ (P Q : Set) : Set where
    andI : P -> Q -> P /\ Q

--   Not allowed if we have proof irrelevance
--   data _\/_ (P Q : Set) : Set where
--     orIL : P -> P \/ Q
--     orIR : Q -> P \/ Q

module Setoid where

  data Setoid : Set1 where
    setoid : (A     : Set)
          -> (_==_  : A -> A -> Set)
          -> (refl  : (x : A) -> x == x)
          -> (sym   : (x y : A) -> x == y -> y == x)
          -> (trans : (x y z : A) -> x == y -> y == z -> x == z)
          -> Setoid

  El : Setoid -> Set
  El (setoid A _ _ _ _) = A

  module Projections where

    eq : (A : Setoid) -> El A -> El A -> Set
    eq (setoid _ e _ _ _) = e

    refl : (A : Setoid) -> {x : El A} -> eq A x x
    refl (setoid _ _ r _ _) = r _

    sym : (A : Setoid) -> {x y : El A} -> (h : eq A x y) -> eq A y x
    sym (setoid _ _ _ s _) = s _ _

    trans : (A : Setoid) -> {x y z : El A} -> eq A x y -> eq A y z -> eq A x z
    trans (setoid _ _ _ _ t) = t _ _ _

  module Equality (A : Setoid) where

    infix 6 _==_

    _==_ : El A -> El A -> Set
    _==_ = Projections.eq A

    refl : {x : El A} -> x == x
    refl = Projections.refl A

    sym : {x y : El A} -> x == y -> y == x
    sym = Projections.sym A

    trans : {x y z : El A} -> x == y -> y == z -> x == z
    trans = Projections.trans A

module EqChain (A : Setoid.Setoid) where

  infixl 5 _===_ _=-=_
  infix  8 _since_

  open Setoid
  private open module EqA = Equality A

  eqProof>_ : (x : El A) -> x == x
  eqProof> x = refl

  _=-=_ : (x : El A) -> {y : El A} -> x == y -> x == y
  x =-= eq = eq

  _===_ : {x y z : El A} -> x == y -> y == z -> x == z
  _===_ = trans

  _since_ : {x : El A} -> (y : El A) -> x == y -> x == y
  _ since eq = eq

module Fun where

  open Logic
  open Setoid

  infixr 10 _=>_ _==>_

  open Setoid.Projections using (eq)

  data _=>_ (A B : Setoid) : Set where
    lam : (f : El A -> El B)
       -> ({x y : El A} -> eq A x y
                         -> eq B (f x) (f y)
          )
       -> A => B

  app : {A B : Setoid} -> (A => B) -> El A -> El B
  app (lam f _) = f

  cong : {A B : Setoid} -> (f : A => B) -> {x y : El A} ->
         eq A x y -> eq B (app f x) (app f y)
  cong (lam _ resp) = resp

  data EqFun {A B : Setoid}(f g : A => B) : Set where
    eqFunI : ({x y : El A} -> eq A x y -> eq B (app f x) (app g y)) ->
             EqFun f g

  eqFunE : {A B : Setoid} -> {f g : A => B} -> {x y : El A} ->
           EqFun f g -> eq A x y -> eq B (app f x) (app g y)
  eqFunE (eqFunI h) = h

  _==>_ : Setoid -> Setoid -> Setoid
  A ==> B = setoid (A => B) EqFun r s t
    where
      module Proof where
        open module EqChainB = EqChain B
        module EqA = Equality A
        open module EqB = Equality B

        -- either abstract or --proof-irrelevance needed
        -- (we don't want to compare the proofs for equality)
        -- abstract
        r : (f : A => B) -> EqFun f f
        r f = eqFunI (\xy -> cong f xy)

        s : (f g : A => B) -> EqFun f g -> EqFun g f
        s f g fg =
          eqFunI (\{x}{y} xy ->
            app g x =-= app g y  since  cong g xy
                    === app f x  since  sym (eqFunE fg xy)
                    === app f y  since  cong f xy
          )

        t : (f g h : A => B) -> EqFun f g -> EqFun g h -> EqFun f h
        t f g h fg gh =
          eqFunI (\{x}{y} xy ->
            app f x =-= app g y  since  eqFunE fg xy
                    === app g x  since  cong g (EqA.sym xy)
                    === app h y  since  eqFunE gh xy
          )
      open Proof

  infixl 100 _$_
  _$_ : {A B : Setoid} -> El (A ==> B) -> El A -> El B
  _$_ = app

  lam2 : {A B C : Setoid} ->
         (f : El A -> El B -> El C) ->
         ({x x' : El A} -> eq A x x' ->
          {y y' : El B} -> eq B y y' -> eq C (f x y) (f x' y')
         ) -> El (A ==> B ==> C)
  lam2 {A} f h = lam (\x -> lam (\y -> f x y)
                                (\y -> h EqA.refl y))
                     (\x -> eqFunI (\y -> h x y))
    where
      module EqA = Equality A

  lam3 : {A B C D : Setoid} ->
         (f : El A -> El B -> El C -> El D) ->
         ({x x' : El A} -> eq A x x' ->
          {y y' : El B} -> eq B y y' ->
          {z z' : El C} -> eq C z z' -> eq D (f x y z) (f x' y' z')
         ) -> El (A ==> B ==> C ==> D)
  lam3 {A} f h =
    lam (\x -> lam2 (\y z -> f x y z)
                    (\y z -> h EqA.refl y z))
        (\x -> eqFunI (\y -> eqFunI (\z -> h x y z)))
    where
      module EqA = Equality A

  eta : {A B : Setoid} -> (f : El (A ==> B)) ->
        eq (A ==> B) f (lam (\x -> f $ x) (\xy -> cong f xy))
  eta f = eqFunI (\xy -> cong f xy)

  id : {A : Setoid} -> El (A ==> A)
  id = lam (\x -> x) (\x -> x)

  {- Now it looks okay. But it's incredibly slow!  Proof irrelevance makes it
     go fast again...  The problem is equality checking of (function type)
     setoids which without proof irrelevance checks equality of the proof that
     EqFun is an equivalence relation.  It's not clear why using lam3 involves
     so many more equality checks than using lam. Making the proofs abstract
     makes the problem go away.
  -}
  compose : {A B C : Setoid} -> El ((B ==> C) ==> (A ==> B) ==> (A ==> C))
  compose =
    lam3 (\f g x -> f $ (g $ x))
         (\f g x -> eqFunE f (eqFunE g x))

  _∘_ : {A B C : Setoid} -> El (B ==> C) -> El (A ==> B) -> El (A ==> C)
  f ∘ g = compose $ f $ g

  const : {A B : Setoid} -> El (A ==> B ==> A)
  const = lam2 (\x y -> x) (\x y -> x)

module Nat where

  open Logic
  open Setoid
  open Fun

  infixl 10 _+_

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  module NatSetoid where

    eqNat : Nat -> Nat -> Set
    eqNat zero     zero   = True
    eqNat zero    (suc _) = False
    eqNat (suc _)  zero   = False
    eqNat (suc n) (suc m) = eqNat n m

    data EqNat (n m : Nat) : Set where
      eqnat : eqNat n m -> EqNat n m

    uneqnat : {n m : Nat} -> EqNat n m -> eqNat n m
    uneqnat (eqnat x) = x

    r : (x : Nat) -> eqNat x x
    r zero    = tt
    r (suc n) = r n

    -- reflexivity of EqNat
    rf : (n : Nat) -> EqNat n n 
    rf = \ x -> eqnat (r x)

    s : (x y : Nat) -> eqNat x y -> eqNat y x
    s  zero    zero   _ = tt
    s (suc n) (suc m) h = s n m h
    s zero    (suc _) ()
    s (suc _) zero    ()

    -- symmetry of EqNat
    sy : (x y : Nat) -> EqNat x y -> EqNat y x
    sy = \x y h -> eqnat (s x y (uneqnat h))

    t : (x y z : Nat) -> eqNat x y -> eqNat y z -> eqNat x z
    t  zero    zero    z      xy yz = yz
    t (suc x) (suc y) (suc z) xy yz = t x y z xy yz
    t  zero   (suc _)  _      () _
    t (suc _)  zero    _      () _
    t (suc _) (suc _)  zero   _  ()

    -- transitivity of EqNat
    tr : (x y z : Nat) -> EqNat x y -> EqNat y z -> EqNat x z
    tr = \x y z xy yz -> eqnat (t x y z (uneqnat xy) (uneqnat yz))

  NAT : Setoid
  NAT = setoid Nat NatSetoid.EqNat NatSetoid.rf NatSetoid.sy NatSetoid.tr

  _+_ : Nat -> Nat -> Nat
  zero  + m = m
  suc n + m = suc (n + m)

  plus : El (NAT ==> NAT ==> NAT)
  plus = lam2 (\n m -> n + m) eqPlus
    where
      module EqNat = Equality NAT
      open EqNat
      open NatSetoid

      eqPlus : {n n' : Nat} -> n == n' -> {m m' : Nat} -> m == m' -> n + m == n' + m'
      eqPlus {zero}  {zero}    _  mm = mm
      eqPlus {suc n} {suc n'}  (eqnat nn) {m}{m'} (eqnat mm) =
        eqnat (uneqnat (eqPlus{n}{n'} (eqnat nn)
                              {m}{m'} (eqnat mm)
              )        )
      eqPlus {zero}  {suc _}  (eqnat ())  _
      eqPlus {suc _} {zero}   (eqnat ())  _

module List where

  open Logic
  open Setoid

  data List (A : Set) : Set where
    nil  : List A
    _::_ : A -> List A -> List A

  LIST : Setoid -> Setoid
  LIST A = setoid (List (El A)) eqList r s t
    where
      module EqA = Equality A
      open EqA

      eqList : List (El A) -> List (El A) -> Set
      eqList nil        nil      = True
      eqList nil       (_ :: _)  = False
      eqList (_ :: _)   nil      = False
      eqList (x :: xs) (y :: ys) = x == y /\ eqList xs ys

      r : (x : List (El A)) -> eqList x x
      r  nil      = tt
      r (x :: xs) = andI refl (r xs)

      s : (x y : List (El A)) -> eqList x y -> eqList y x
      s  nil       nil       h            = h
      s (x :: xs) (y :: ys) (andI xy xys) = andI (sym xy) (s xs ys xys)
      s  nil      (_ :: _)  ()
      s (_ :: _)   nil      ()

      t : (x y z : List (El A)) -> eqList x y -> eqList y z -> eqList x z
      t  nil       nil       zs        _             h            = h
      t (x :: xs) (y :: ys) (z :: zs) (andI xy xys) (andI yz yzs) =
        andI (trans xy yz) (t xs ys zs xys yzs)
      t  nil      (_ :: _)  _          () _
      t (_ :: _)   nil      _          () _
      t (_ :: _)  (_ :: _)  nil        _  ()

open Fun

