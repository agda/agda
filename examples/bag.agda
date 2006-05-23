
module Top where

module Prelude where

  id : {a : Set} -> a -> a
  id x = x

  infixr 0 $

  ($) : {a, b : Set} -> (a -> b) -> a -> b
  f $ x = f x

  data Bool : Set where
    True  : Bool
    False : Bool

  data Pair (a, b : Set) : Set where
    pair : a -> b -> Pair a b

  fst : {a, b : Set} -> Pair a b -> a
  fst (pair x y) = x

  snd : {a, b : Set} -> Pair a b -> b
  snd (pair x y) = y

  data Either (a, b : Set) : Set where
    left  : a -> Either a b
    right : b -> Either a b

  data Unit : Set where
    unit : Unit

  data Absurd : Set where

  data Not (a : Set) : Set where
    not : (a -> Absurd) -> Not a

  -- Not : Set -> Set
  -- Not a = a -> Absurd

  contrapositive : {a, b : Set} -> (a -> b) -> Not b -> Not a
  contrapositive p (not nb) = not (\a -> nb (p a))

  private
    notDistribOut' : {a, b : Set} -> Not a -> Not b -> Either a b -> Absurd
    notDistribOut' (not na) _        (left a)  = na a
    notDistribOut' _        (not nb) (right b) = nb b

  notDistribOut : {a, b : Set} -> Not a -> Not b -> Not (Either a b)
  notDistribOut na nb = not (notDistribOut' na nb)

  notDistribIn : {a, b : Set} -> Not (Either a b) -> Pair (Not a) (Not b)
  notDistribIn (not nab) = pair (not (\a -> nab (left a)))
                                (not (\b -> nab (right b)))

module Equiv where

  open Prelude

  data Equiv (a : Set) : Set1 where
    equiv :  ((==) : a -> a -> Set)
          -> (refl  : (x : a) -> x == x)
          -> (sym   : (x, y : a) -> x == y -> y == x)
          -> (trans : (x, y, z : a) -> x == y -> y == z -> x == z)
          -> Equiv a

  rel : {a : Set} -> Equiv a -> (a -> a -> Set)
  rel (equiv (==) _ _ _) = (==)

  data Decidable {a : Set} ((==) : a -> a -> Set) : Set where
    dec : ((x, y : a) -> Either (x == y) (Not (x == y))) -> Decidable (==)

  data DecidableEquiv (a : Set) : Set1 where
    decEquiv : (eq : Equiv a) -> Decidable (rel eq) -> DecidableEquiv a

  rel' :  {a : Set} -> (eq : DecidableEquiv a) -> (a -> a -> Set)
  rel' (decEquiv eq _) = rel eq

  refl : {a : Set} -> (eq : DecidableEquiv a) -> {x : a} -> rel' eq x x
  refl (decEquiv (equiv _ refl' _ _) _) = refl' _

  sym : {a : Set} -> (eq : DecidableEquiv a) -> {x, y : a}
      -> rel' eq x y -> rel' eq y x
  sym (decEquiv (equiv _ _ sym' _) _) = sym' _ _

  trans : {a : Set} -> (eq : DecidableEquiv a) -> {x, y, z : a}
      -> rel' eq x y -> rel' eq y z -> rel' eq x z
  trans (decEquiv (equiv _ _ _ trans') _) = trans' _ _ _

  decRel :  {a : Set} -> (eq : DecidableEquiv a) -> (x, y : a)
         -> Either (rel' eq x y) (Not (rel' eq x y))
  decRel (decEquiv _ (dec f)) = f

  private

    decRelI :  {a : Set} -> ((==) : a -> a -> Set) -> {x, y : a}
             -> Either (x == y) (Not (x == y)) -> Bool
    decRelI _ (left _)  = True
    decRelI _ (right _) = False

  decRel' : {a : Set} -> DecidableEquiv a -> (a -> a -> Bool)
  decRel' eq x y = decRelI (rel' eq) (decRel eq x y)

module Datoid where

  open Prelude
  open Equiv

  data Datoid : Set1 where
    datoid : (a : Set) -> DecidableEquiv a -> Datoid

  El : Datoid -> Set
  El (datoid a _) = a

  datoidEq : (a : Datoid) -> DecidableEquiv (El a)
  datoidEq (datoid _ eq) = eq

  datoidRel : (a : Datoid) -> El a -> El a -> Set
  datoidRel d = rel' (datoidEq d)

  dRefl : (a : Datoid) -> {x : El a} -> datoidRel a x x
  dRefl a = refl (datoidEq a)

  dSym : (a : Datoid) -> {x, y : El a}
      -> datoidRel a x y -> datoidRel a y x
  dSym a = sym (datoidEq a)

  dTrans : (a : Datoid) -> {x, y, z : El a}
      -> datoidRel a x y -> datoidRel a y z -> datoidRel a x z
  dTrans a = trans (datoidEq a)

  pairDatoid : Datoid -> Datoid -> Datoid
  pairDatoid a b = datoid (Pair (El a) (El b)) ?

module Eq where

  data (=^=) {a : Set} (x, y : a) : Set1 where
    leibniz : ((P : a -> Set) -> P x -> P y) -> x =^= y

  leibnizRefl : {a : Set} -> (x : a) -> x =^= x
  leibnizRefl x = leibniz (\P p -> p)

module Nat where

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  one : Nat
  one = suc zero

  (+) : Nat -> Nat -> Nat
  zero  + n = n
  suc m + n = suc (m + n)

module Pos where

  abstract

    Pos : Set
    Pos = Nat.Nat

    one : Pos
    one = Nat.zero

    suc : Pos -> Pos
    suc = Nat.suc

    suc' : Nat.Nat -> Pos
    suc' n = n

    (+) : Pos -> Pos -> Pos
    m + n = suc (Nat.+ m n)

    toNat : Pos -> Nat.Nat
    toNat = suc

module List where

  open Prelude
  open Equiv
  open Datoid

  data List (a : Set) : Set where
    nil : List a
    (::) : a -> List a -> List a

  map : {a, b : Set} -> (a -> b) -> List a -> List b
  map f nil       = nil
  map f (x :: xs) = f x :: map f xs

  member : (a : Datoid) -> El a -> List (El a) -> Set
  member _ x nil       = Absurd
  member a x (y :: ys) = Either (rel' (datoidEq a) x y) (member a x ys)

  memberPreservesEq
    :  {a : Datoid}
    -> {x, y : El a}
    -> datoidRel a x y
    -> (zs : List (El a))
    -> member a x zs
    -> member a y zs
  memberPreservesEq     xy nil       abs         = abs
  memberPreservesEq {a} xy (z :: zs) (left xz)   =
    left  (dTrans a (dSym a xy) xz)
  memberPreservesEq     xy (z :: zs) (right xzs) =
    right (memberPreservesEq xy zs xzs)

  NoDuplicates : (a : Datoid) -> List (El a) -> Set
  NoDuplicates _ nil      = Unit
  NoDuplicates a (x :: b) = Pair (Not (member a x b)) (NoDuplicates a b)

  listDatoid : Datoid -> Datoid
  listDatoid a = datoid (List (El a)) (decEquiv ? ?)

module Bag where

  open Prelude
  open Equiv
  open Datoid
  open Eq
  open Nat
  open List

  private

    data BagType (a : Datoid) : Set where
      bt : List (Pair Pos.Pos (El a)) -> BagType a

    postulate

      BagEquiv : (a : Datoid) -> DecidableEquiv (BagType a)

  abstract

    Bag : Datoid -> Datoid
    Bag a = datoid (BagType a) (BagEquiv a)

    empty : {a : Datoid} -> El (Bag a)
    empty = bt nil

    private
      lookup' :  {a : Datoid} -> Pos.Pos -> El a -> El (Bag a) -> Bool
              -> Pair Nat (El (Bag a)) -> Pair Nat (El (Bag a))
      lookup' n _ b True  _                 = pair (Pos.toNat n) b
      lookup' n y _ False (pair n' (bt b')) = pair n' (bt (pair n y :: b'))

    lookup : {a : Datoid} -> El a -> El (Bag a) -> Pair Nat (El (Bag a))
    lookup     x (bt nil)             = pair zero (bt nil)
    lookup {a} x (bt (pair n y :: b)) =
      lookup' n y (bt b) (decRel' (datoidEq a) x y) (lookup x (bt b))

    private
      insert' : {a : Datoid} -> El a -> Pair Nat (El (Bag a)) -> El (Bag a)
      insert' x (pair n (bt b)) = bt (pair (Pos.suc' n) x :: b)

    insert : {a : Datoid} -> El a -> El (Bag a) -> El (Bag a)
    insert x b = insert' x (lookup x b)

    data Traverse (a : Datoid) : Set where
      Empty  : Traverse a
      Insert : (x : El a) -> (b : El (Bag a)) -> Traverse a

    run : {a : Datoid} -> Traverse a -> El (Bag a)
    run Empty        = empty
    run (Insert x b) = insert x b

  postulate

    traverse : {a : Datoid} -> El (Bag a) -> Traverse a
  --   traverse nil                         = Empty
  --   -- traverse (pair zero x :: b) = -- Missing case.
  --   traverse (pair (suc zero)    x :: b) = Insert x b
  --   traverse (pair (suc (suc n)) x :: b) = Insert x (pair (suc n) x :: b)

    traverseTraverses
      :  {a : Datoid} -> (b : El (Bag a)) -> run (traverse b) =^= b
  --   traverseTraverses (==) nil                      = leibnizRefl nil
  --   -- traverseTraverses (==) (pair zero    x :: b) = -- Missing case.
  --   traverseTraverses (==) (pair (suc zero) x :: b) =
  --     -- We can't show that b doesn't contain any x-s.
  --     -- insert (==) x b =^= (pair (suc zero) x :: b)
  --   traverseTraverses (==) (pair (suc (suc n)) x :: b) =
  --     -- Possible if DecidableEquiv includes substitutivity.

  private

    postulate

      bagElim'
        :  {a : Datoid}
        -> (P : El (Bag a) -> Set)
        -> P empty
        -> ((x : El a) -> (b : El (Bag a)) -> P b -> P (insert x b))
        -> (b : El (Bag a))
        -> (t : Traverse a)
        -> run t =^= b
        -> P b
  --     bagElim' P e i b Empty         (leibniz subst) = subst P e
  --     bagElim' P e i b (Insert x b') (leibniz subst) =
  --       subst P (i x b' (bagElim' P e i b' (traverse b')
  --                                          (traverseTraverses b')))

  postulate

    bagElim
      :  {a : Datoid}
      -> (P : El (Bag a) -> Set)
      -> P empty
      -> ((x : El a) -> (b : El (Bag a)) -> P b -> P (insert x b))
      -> (b : El (Bag a))
      -> P b
    -- bagElim P e i b =
    --   bagElim' P e i b (traverse b) (traverseTraverses b)

module ParserC where
  open Prelude
  open Equiv
  open Eq
  open Datoid
  open List
  open Bag

  parserDatoid : (a, s : Datoid) -> Datoid
  parserDatoid a s = pairDatoid a (listDatoid s)

-- We use the following datatype instead of
--   type Parsing s a = [s] -> Bag (a, [s])
  data Parsing (s, a : Datoid) : Set1 where
    P :  (List (El s) -> El (Bag (parserDatoid a s)))
      -> Parsing s a


-- insert : {a : Datoid} -> El a -> El (Bag a) -> El (Bag a)
-- pairDatoid : Datoid -> Datoid -> Datoid
--(empty {Bag (pairDatoid s (listDatoid s))})
--  bagElim
--    :  {a : Datoid}
--    -> (P : El (Bag a) -> Set)
--    -> P empty
--    -> ((x : El a) -> (b : El (Bag a)) -> P b -> P (insert x b))
--    -> (b : El (Bag a))
--    -> P b

  private
    (<+>) :  {s, a : Datoid}
          -> El (Bag (parserDatoid a s))
          -> El (Bag (parserDatoid a s))
          -> El (Bag (parserDatoid a s))
    x <+> y = bagElim (\bs -> El (Bag (parserDatoid _ _)))
		      y
		      (\z zs ih -> insert z ih)
		      x
{-
    symbol' :  {s : Datoid} -> List (El s) -> El (Bag (parserDatoid s s))
    symbol' nil       = empty
    symbol' (x :: xs) = insert (pair x xs) empty

  symbol : {s : Datoid} -> Parsing s s
  symbol = P symbol'

  fail : {s, a : Datoid} -> Parsing s a
  fail = P (\ss -> empty)

  (+++) : {s, a : Datoid} -> Parsing s a -> Parsing s a -> Parsing s a
  P p +++ P q = P (\s -> p s <+> q s)

--   return :  {s, a : Datoid} -> (x : a) -> Parsing s a
--   return = \x s -> P (insert (pair x s) empty)
-}
