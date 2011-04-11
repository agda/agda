
module Prelude where

  id : {a : Set} -> a -> a
  id x = x

  infixr 0 _$_

  _$_ : {a b : Set} -> (a -> b) -> a -> b
  f $ x = f x

  data Bool : Set where
    True  : Bool
    False : Bool

  _&&_ : Bool -> Bool -> Bool
  True  && b = b
  False && _ = False

  data Pair (a b : Set) : Set where
    pair : a -> b -> Pair a b

  fst : {a b : Set} -> Pair a b -> a
  fst (pair x y) = x

  snd : {a b : Set} -> Pair a b -> b
  snd (pair x y) = y

  data Either (a b : Set) : Set where
    left  : a -> Either a b
    right : b -> Either a b

  data Maybe (a : Set) : Set where
    Nothing : Maybe a
    Just    : a -> Maybe a

  data Unit : Set where
    unit : Unit

  data Absurd : Set where

  absurdElim : {whatever : Set} -> Absurd -> whatever
  absurdElim ()

--   data Pi {a : Set} (f : a -> Set) : Set where
--     pi : ((x : a) -> f x) -> Pi f
-- 
--   apply : {a : Set} -> {f : a -> Set} -> Pi f -> (x : a) -> f x
--   apply (pi f) x = f x

  T : Bool -> Set
  T True  = Unit
  T False = Absurd

  andT : {x y : Bool} -> T x -> T y -> T (x && y)
  andT {True}  {True}  _  _ = unit
  andT {True}  {False} _  ()
  andT {False} {_}     () _

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

  Dec : (A : Set) -> Set
  Dec A = Either A (Not A)
 