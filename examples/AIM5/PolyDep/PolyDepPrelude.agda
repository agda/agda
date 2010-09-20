module PolyDepPrelude where

data Pi {X : Set} (Y : X -> Set) : Set where
  pi : ((x : X) -> Y x) -> Pi Y

apply : {a : Set} -> {f : a -> Set} -> Pi f -> (x : a) -> f x
apply (pi f) x = f x

data Forall {X : Set} (Y : X -> Set) : Set where
  forAll : ((x : X) -> Y x) -> Forall Y

data _=>_ (X Y : Set) : Set where
  lam : (X -> Y) -> X => Y

_$$_ : {X Y : Set} -> (X => Y) -> X -> Y
lam f $$ x = f x


infixr 0 _$$_

id : {a : Set} -> a -> a
id x = x

infixr 0 _$_

_$_ : {a b : Set} -> (a -> b) -> a -> b
f $ x = f x

data Bool : Set where
  true  : Bool
  false : Bool

_&&_ : Bool -> Bool -> Bool
true  && b = b
false && _ = false

data Pair (a b : Set) : Set where
  pair : a -> b -> Pair a b

fst : {a b : Set} -> Pair a b -> a
fst (pair x y) = x

snd : {a b : Set} -> Pair a b -> b
snd (pair x y) = y

cmp : {X Y Z : Set} -> (Y -> Z) -> (X -> Y) -> X -> Z
cmp f g = \x -> f (g x)

data Either (a b : Set) : Set where
  left  : a -> Either a b
  right : b -> Either a b

data Maybe (a : Set) : Set where
  Nothing : Maybe a
  Just    : a -> Maybe a

data Unit : Set where
  unit : Unit

Taut = Unit


data Absurd : Set where

postulate
  absurdElim : {whatever : Set} -> Absurd -> whatever

T : Bool -> Set
T true  = Unit
T false = Absurd

andT : {x y : Bool} -> T x -> T y -> T (x && y)
andT {true}  {true}  _  _ = unit
andT {false} {_}     () _
andT {true}  {false} _  ()

T' : {a : Set} -> (a -> a -> Bool) -> (a -> a -> Set)
T' f x y = T (f x y)

data Not (a : Set) : Set where
  not : (a -> Absurd) -> Not a

-- Not : Set -> Set
-- Not a = a -> Absurd

contrapositive : {a b : Set} -> (a -> b) -> Not b -> Not a
contrapositive p (not nb) = not (\a -> nb (p a))

private
  notDistribOut' : {a b : Set} -> Not a -> Not b -> Either a b -> Absurd
  notDistribOut' (not na) _        (left a)  = na a
  notDistribOut' _        (not nb) (right b) = nb b

notDistribOut : {a b : Set} -> Not a -> Not b -> Not (Either a b)
notDistribOut na nb = not (notDistribOut' na nb)

notDistribIn : {a b : Set} -> Not (Either a b) -> Pair (Not a) (Not b)
notDistribIn (not nab) = pair (not (\a -> nab (left a)))
                              (not (\b -> nab (right b)))

data _<->_ (a b : Set) : Set where
  iff : (a -> b) -> (b -> a) -> a <-> b

iffLeft : {a b : Set} -> (a <-> b) -> (a -> b)
iffLeft (iff l _) = l

iffRight : {a b : Set} -> (a <-> b) -> (b -> a)
iffRight (iff _ r) = r

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

one : Nat
one = suc zero

elimNat : (C : Nat -> Set)
         -> (C zero) -> ((m : Nat) -> C m -> C (suc m)) -> (n : Nat) -> C n
elimNat C c_z c_s zero = c_z
elimNat C c_z c_s (suc m') = c_s m' (elimNat C c_z c_s m')

data List (A : Set) : Set where
  nil  : List A
  _::_ : A -> List A -> List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL  nil  #-}
{-# BUILTIN CONS _::_ #-}

elimList : {A : Set} ->
          (C : List A -> Set) ->
          (C nil) ->
          ((a : A) -> (as : List A) -> C as -> C (a :: as)) ->
          (as : List A) ->
          C as
elimList _ c_nil _ nil = c_nil
elimList C c_nil c_con (a :: as) = c_con a as (elimList C c_nil c_con as)

data Reflexive {X : Set} (_R_ : X -> X -> Set) : Set where
  reflexive : ((x : X) -> x R x) -> Reflexive _R_
data Symmetrical {X : Set} (_R_ : X -> X -> Set) : Set where
  symmetrical : ( {x1 x2 : X} -> x1 R x2 -> x2 R x1) -> Symmetrical _R_
data Substitutive {X : Set} (_R_ : X -> X -> Set) : Set1 where
  substitutive : ( (P : X -> Set) -> {x1 x2 : X} -> x1 R x2 -> P x1 -> P x2)
                 -> Substitutive _R_

True : Bool -> Set
True (true)  = Unit
True (false) = Absurd

data Datoid  : Set1 where
  datoid : (Elem : Set) ->
           (eq : Elem -> Elem -> Bool) ->
           (ref : (x : Elem) -> True (eq x x)) ->
           (subst : Substitutive  (\x1 -> \x2 -> True (eq x1 x2))) ->
           Datoid

pElem : Datoid -> Set
pElem (datoid Elem _ _ _) = Elem

