module Top where

module Prelude where

  id : {a : Set} -> a -> a
  id x = x

  infixr 0 _$_

  _$_ : {a, b : Set} -> (a -> b) -> a -> b
  f $ x = f x

  data Bool : Set where
    True  : Bool
    False : Bool

  _&&_ : Bool -> Bool -> Bool
  True  && b = b
  False && _ = False

  data Pair (a, b : Set) : Set where
    pair : a -> b -> Pair a b

  fst : {a, b : Set} -> Pair a b -> a
  fst (pair x y) = x

  snd : {a, b : Set} -> Pair a b -> b
  snd (pair x y) = y

  data Either (a, b : Set) : Set where
    left  : a -> Either a b
    right : b -> Either a b

  data Maybe (a : Set) : Set where
    Nothing : Maybe a
    Just    : a -> Maybe a

  data Unit : Set where
    unit : Unit

  data Absurd : Set where

  postulate
    absurdElim : {whatever : Set} -> Absurd -> whatever

  data Pi {a : Set} (f : a -> Set) : Set where
    pi : ((x : a) -> f x) -> Pi f

  apply : {a : Set} -> {f : a -> Set} -> Pi f -> (x : a) -> f x
  apply (pi f) x = f x

  T : Bool -> Set
  T True  = Unit
  T False = Absurd

  andT : {x, y : Bool} -> T x -> T y -> T (x && y)
  andT {True} {True} _ _ = unit

  T' : {a : Set} -> (a -> a -> Bool) -> (a -> a -> Set)
  T' f x y = T (f x y)

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

  data _<->_ (a, b : Set) : Set where
    iff : (a -> b) -> (b -> a) -> a <-> b

  iffLeft : {a, b : Set} -> (a <-> b) -> (a -> b)
  iffLeft (iff l _) = l

  iffRight : {a, b : Set} -> (a <-> b) -> (b -> a)
  iffRight (iff _ r) = r

module Eq where

  open Prelude

  abstract
    data _=^=_ {a : Set} (x, y : a) : Set1 where
      leibniz : ((P : a -> Set) -> P x <-> P y) -> x =^= y

    leibnizSubst :  {a : Set} -> {x, y : a}
                 -> x =^= y -> (P : a -> Set) -> P x -> P y
    leibnizSubst (leibniz f) P p = iffLeft (f P) p

    leibnizRefl : {a : Set} -> {x : a} -> x =^= x
    leibnizRefl = leibniz (\_ -> iff id id)

    leibnizSym : {a : Set} -> {x, y : a} -> x =^= y -> y =^= x
    leibnizSym (leibniz f) =
      leibniz (\P -> iff (iffRight (f P)) (iffLeft (f P)))

module Equiv where

  open Prelude
  open Eq

  data Equiv (a : Set) : Set1 where
    equiv :  (_==_  : a -> a -> Set)
          -> (refl  : (x : a) -> x == x)
          -> (sym   : (x, y : a) -> x == y -> y == x)
          -> (trans : (x, y, z : a) -> x == y -> y == z -> x == z)
          -> Equiv a

  rel : {a : Set} -> Equiv a -> (a -> a -> Set)
  rel (equiv _==_ _ _ _) = _==_

  data Decidable {a : Set} (eq : a -> a -> Set) : Set where
    dec : ((x, y : a) -> Either (eq x y) (Not (eq x y))) -> Decidable eq

  private
    boolFunctionsDecidable'
      : {a : Set}
      -> (f : a -> a -> Bool)
      -> (x, y : a)
      -> (b : Bool)
      -> (b =^= f x y)
      -> Either (T' f x y) (Not (T' f x y))
    boolFunctionsDecidable' eq x y True  eq = left (leibnizSubst eq T unit)
    boolFunctionsDecidable' eq x y False eq =
      right (not (\xy -> leibnizSubst (leibnizSym eq) T xy))

  boolFunctionsDecidable
    : {a : Set} -> (f : a -> a -> Bool) -> Decidable (T' f)
  boolFunctionsDecidable f =
    dec (\x y -> boolFunctionsDecidable' f x y (f x y) leibnizRefl)

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

    decRelI :  {a : Set} -> (eq : a -> a -> Set) -> {x, y : a}
             -> Either (eq x y) (Not (eq x y)) -> Bool
    decRelI _ (left _)  = True
    decRelI _ (right _) = False

  decRel' : {a : Set} -> DecidableEquiv a -> (a -> a -> Bool)
  decRel' eq x y = decRelI (rel' eq) (decRel eq x y)

  private
    pairEq :  {a, b : Set} -> DecidableEquiv a -> DecidableEquiv b
           -> (p1, p2 : Pair a b) -> Set
    pairEq a b (pair x1 x2) (pair y1 y2) = Pair (rel' a x1 y1) (rel' b x2 y2)

    refl' :  {a, b : Set} -> (da : DecidableEquiv a) -> (db : DecidableEquiv b)
          -> (x : Pair a b) -> pairEq da db x x
    refl' a b (pair x1 x2) = pair (refl a) (refl b)

    sym' :  {a, b : Set} -> (da : DecidableEquiv a) -> (db : DecidableEquiv b)
         -> (x, y : Pair a b) -> pairEq da db x y -> pairEq da db y x
    sym' a b (pair x1 x2) (pair y1 y2) (pair xy1 xy2) =
      pair (sym a xy1) (sym b xy2)

    trans'
      :  {a, b : Set} -> (da : DecidableEquiv a) -> (db : DecidableEquiv b)
      -> (x, y, z : Pair a b)
      -> pairEq da db x y -> pairEq da db y z -> pairEq da db x z
    trans' a b (pair x1 x2) (pair y1 y2)
           (pair z1 z2) (pair xy1 xy2) (pair yz1 yz2) =
      pair (trans a xy1 yz1) (trans b xy2 yz2)

    dec'' :  {a, b : Set} -> {da : DecidableEquiv a} -> {db : DecidableEquiv b}
          -> {x1, y1 : a} -> {x2, y2 : b}
          -> Either (rel' da x1 y1) (Not (rel' da x1 y1))
          -> Either (rel' db x2 y2) (Not (rel' db x2 y2))
          -> Either (pairEq da db (pair x1 x2) (pair y1 y2))
                    (Not (pairEq da db (pair x1 x2) (pair y1 y2)))
    dec'' (left xy1)         (left xy2)         = left (pair xy1 xy2)
    dec'' _                  (right (not nxy2)) =
      right (not (\xy -> nxy2 (snd xy)))
    dec'' (right (not nxy1)) (left _)           =
      right (not (\xy -> nxy1 (fst xy)))

    dec' :  {a, b : Set} -> (da : DecidableEquiv a) -> (db : DecidableEquiv b)
         -> (x, y : Pair a b) -> Either (pairEq da db x y) _
    dec' a b (pair x1 x2) (pair y1 y2) =
      dec'' {_} {_} {a} {b} (decRel a x1 y1) (decRel b x2 y2)

  pairEquiv
    :  {a, b : Set} -> DecidableEquiv a -> DecidableEquiv b
    -> DecidableEquiv (Pair a b)
  pairEquiv a b = decEquiv (equiv (pairEq a b)
                                  (refl' a b) (sym' a b) (trans' a b))
                           (dec (dec' a b))

module Datoid where

  open Equiv
  open Prelude

  data Datoid : Set1 where
    datoid : (a : Set) -> DecidableEquiv a -> Datoid

  El : Datoid -> Set
  El (datoid a _) = a

  datoidEq : (a : Datoid) -> DecidableEquiv (El a)
  datoidEq (datoid _ eq) = eq

  datoidRel : (a : Datoid) -> El a -> El a -> Set
  datoidRel d = rel' (datoidEq d)

  datoidDecRel :  (a : Datoid) -> (x, y : El a)
               -> Either (datoidRel a x y) (Not (datoidRel a x y))
  datoidDecRel d = decRel (datoidEq d)

  dRefl : (a : Datoid) -> {x : El a} -> datoidRel a x x
  dRefl a = refl (datoidEq a)

  dSym : (a : Datoid) -> {x, y : El a}
      -> datoidRel a x y -> datoidRel a y x
  dSym a = sym (datoidEq a)

  dTrans : (a : Datoid) -> {x, y, z : El a}
      -> datoidRel a x y -> datoidRel a y z -> datoidRel a x z
  dTrans a = trans (datoidEq a)

  data Respects (a : Datoid) (P : El a -> Set) : Set where
    respects : ((x, y : El a) -> datoidRel a x y -> P x -> P y) -> Respects a P

  subst :  {a : Datoid} -> {P : El a -> Set} -> Respects a P
        -> (x, y : El a) -> datoidRel a x y -> P x -> P y
  subst (respects f) = f

  pairDatoid : (a, b : Datoid) -> Datoid
  pairDatoid a b = datoid (Pair (El a) (El b))
                          (pairEquiv (datoidEq a) (datoidEq b))

module Nat where

  open Prelude
  open Equiv
  open Datoid

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  one : Nat
  one = suc zero

  _+_ : Nat -> Nat -> Nat
  zero  + n = n
  suc m + n = suc (m + n)

  private
    eqNat : Nat -> Nat -> Bool
    eqNat zero    zero    = True
    eqNat (suc m) (suc n) = eqNat m n
    eqNat _       _       = False

    refl' : (x : Nat) -> T (eqNat x x)
    refl' zero    = unit
    refl' (suc n) = refl' n

    sym' : (x, y : Nat) -> T (eqNat x y) -> T (eqNat y x)
    sym' zero     zero     _     = unit
    sym' (suc n1) (suc n2) eq    = sym' n1 n2 eq
    sym' (suc _)  zero     wrong = wrong
    sym' zero     (suc _)  wrong = wrong

    trans' : (x, y, z : Nat) -> T (eqNat x y) -> T (eqNat y z) -> T (eqNat x z)
    trans' zero     _        zero     _     _     = unit
    trans' (suc n1) (suc n2) (suc n3) eq12  eq23  = trans' n1 n2 n3 eq12 eq23
    trans' zero     (suc _)  _        wrong _     = absurdElim wrong
    trans' _        zero     (suc _)  _     wrong = absurdElim wrong
    trans' (suc _)  zero     _        wrong _     = absurdElim wrong
    trans' _        (suc _)  zero     _     wrong = absurdElim wrong

  decidableEquiv : DecidableEquiv Nat
  decidableEquiv = decEquiv (equiv (T' eqNat) refl' sym' trans')
                            (boolFunctionsDecidable eqNat)

  natDatoid : Datoid
  natDatoid = datoid Nat decidableEquiv

module Pos where

  open Prelude
  open Equiv
  open Datoid

  abstract

    Pos : Set
    Pos = Nat.Nat

    one : Pos
    one = Nat.zero

    suc : Pos -> Pos
    suc = Nat.suc

    suc' : Nat.Nat -> Pos
    suc' n = n

    _+_ : Pos -> Pos -> Pos
    m + n = suc (Nat._+_ m n)

    -- Returns Nothing if input is 1.
    pred : Pos -> Maybe Pos
    pred Nat.zero    = Nothing
    pred (Nat.suc n) = Just n

    toNat : Pos -> Nat.Nat
    toNat = suc

    decidableEquiv : DecidableEquiv Pos
    decidableEquiv = Nat.decidableEquiv

  posDatoid : Datoid
  posDatoid = datoid Pos decidableEquiv

  sucPred : Maybe Pos -> Pos
  sucPred Nothing  = one
  sucPred (Just p) = suc p

  data Pred (p : Pos) (mP : Maybe Pos) : Set where
    ok : datoidRel posDatoid (sucPred mP) p -> Pred p mP

  abstract

    -- Returns Nothing if input is 1.
    predOK : (p : Pos) -> Pred p (pred p)
    predOK Nat.zero    = ok (dRefl posDatoid {one})
    predOK (Nat.suc n) = ok (dRefl posDatoid {suc n})

module List where

  open Prelude
  open Equiv
  open Datoid
  open Nat

  data List (a : Set) : Set where
    nil	 : List a
    _::_ : a -> List a -> List a

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

  private
    noCopies' : (a : Datoid) -> (x, y : El a) -> Either (datoidRel a x y) _
              -> Nat -> Nat
    noCopies' _ _ _ (left _)  n = suc n
    noCopies' _ _ _ (right _) n = n

  noCopies : (a : Datoid) -> El a -> List (El a) -> Nat
  noCopies a x nil       = zero
  noCopies a x (y :: ys) =
    noCopies' a x y (datoidDecRel a x y) (noCopies a x ys)

  NoDuplicates : (a : Datoid) -> List (El a) -> Set
  NoDuplicates _ nil      = Unit
  NoDuplicates a (x :: b) = Pair (Not (member a x b)) (NoDuplicates a b)

  private
    delete'
      : (a : Datoid)
      -> (x, y : El a)
      -> Either (datoidRel a x y) _
      -> (ys, delXYs : List (El a))
      -> List (El a)
    delete' _ _ _ (left _)  ys _      = ys
    delete' _ _ _ (right _) _  delXYs = delXYs

  -- Removes first occurrence, if any.
  delete : (a : Datoid) -> El a -> List (El a) -> List (El a)
  delete a x nil       = nil
  delete a x (y :: ys) = delete' a x y (datoidDecRel a x y) ys (delete a x ys)

  private
    Perm : (a : Datoid) -> (xs, ys : List (El a)) -> Set
    Perm a xs ys = Pi (\z -> datoidRel natDatoid (noCopies a z xs)
                                                 (noCopies a z ys))

    refl' : {a : Datoid} -> (xs : List (El a)) -> Perm a xs xs
    refl' {a} xs = pi (\z -> dRefl natDatoid {noCopies a z xs})

    sym' :  {a : Datoid} -> (xs, ys : List (El a))
         -> Perm a xs ys -> Perm a ys xs
    sym' {a} xs ys (pi xy) =
      pi (\z -> dSym natDatoid {noCopies a z xs} {noCopies a z ys} (xy z))

    trans' : {a : Datoid} -> (xs, ys, zs : List (El a))
           -> Perm a xs ys -> Perm a ys zs -> Perm a xs zs
    trans' {a} xs ys zs (pi xy) (pi yz) =
      pi (\z -> dTrans natDatoid
                       {noCopies a z xs} {noCopies a z ys} {noCopies a z zs}
                       (xy z) (yz z))

    postulate
      dec' : {a : Datoid} -> (xs, ys : List (El a))
             -> Either (Perm a xs ys) (Not (Perm a xs ys))

  Permutation : (a : Datoid) -> DecidableEquiv (List (El a))
  Permutation a = decEquiv (equiv (Perm a) refl' sym' trans') (dec dec')

module Bag where

  open Prelude
  open Equiv
  open Datoid
  open Eq
  open Nat
  open List

  abstract

  ----------------------------------------------------------------------
  -- Bag type

    private
      -- If this were Coq, then the invariant should be a Prop. Similar
      -- remarks apply to some definitions below. Since I have to write
      -- the supporting library myself I can't be bothered to
      -- distinguish Set and Prop right now, though.

      data BagType (a : Datoid) : Set where
        bt :  (pairs : List (Pair Pos.Pos (El a)))
           -> NoDuplicates a (map snd pairs)
           -> BagType a

      list : {a : Datoid} -> BagType a -> List (Pair Pos.Pos (El a))
      list (bt l _) = l

      contents : {a : Datoid} -> BagType a -> List (El a)
      contents b = map snd (list b)

      invariant :  {a : Datoid} -> (b : BagType a)
                -> NoDuplicates a (contents b)
      invariant (bt _ i) = i

    private
      elemDatoid : Datoid -> Datoid
      elemDatoid a = pairDatoid Pos.posDatoid a

      BagEq : (a : Datoid) -> BagType a -> BagType a -> Set
      BagEq a b1 b2 = rel' (Permutation (elemDatoid a)) (list b1) (list b2)

      eqRefl : {a : Datoid} -> (x : BagType a) -> BagEq a x x
      eqRefl {a} x = refl (Permutation (elemDatoid a)) {list x}

      eqSym :  {a : Datoid} -> (x, y : BagType a)
            -> BagEq a x y -> BagEq a y x
      eqSym {a} x y = sym (Permutation (elemDatoid a)) {list x} {list y}

      eqTrans :  {a : Datoid} -> (x, y, z : BagType a)
            -> BagEq a x y -> BagEq a y z -> BagEq a x z
      eqTrans {a} x y z = trans (Permutation (elemDatoid a))
                                {list x} {list y} {list z}

      eqDec : {a : Datoid} -> (x, y : BagType a)
            -> Either (BagEq a x y) _
      eqDec {a} x y = decRel (Permutation (elemDatoid a)) (list x) (list y)

      BagEquiv : (a : Datoid) -> DecidableEquiv (BagType a)
      BagEquiv a = decEquiv (equiv (BagEq a) eqRefl eqSym eqTrans) (dec eqDec)

    Bag : Datoid -> Datoid
    Bag a = datoid (BagType a) (BagEquiv a)

  ----------------------------------------------------------------------
  -- Bag primitives

    empty : {a : Datoid} -> El (Bag a)
    empty = bt nil unit

    private
      data LookupResult (a : Datoid) (x : El a) (b : El (Bag a)) : Set where
        lr :  Nat
           -> (b' : El (Bag a))
           -> Not (member a x (contents b'))
           -> ({y : El a} -> Not (member a y (contents b))
                          -> Not (member a y (contents b')))
           -> LookupResult a x b

      lookup1 :  {a : Datoid}
              -> (n : Pos.Pos)
              -> (y : El a)
              -> (b' : El (Bag a))
              -> (nyb' : Not (member a y (contents b')))
              -> (x : El a)
              -> Either (datoidRel a x y) _
              -> LookupResult a x b'
              -> LookupResult a x (bt (pair n y :: list b')
                                      (pair nyb' (invariant b')))
      lookup1 n y b' nyb' x (left xy) _ =
        lr (Pos.toNat n) b'
           (contrapositive (memberPreservesEq xy (contents b')) nyb')
           (\{y'} ny'b -> snd (notDistribIn ny'b))
      lookup1 {a} n y b' nyb' x (right nxy)
              (lr n' (bt b'' ndb'') nxb'' nmPres) =
        lr n' (bt (pair n y :: b'') (pair (nmPres nyb') ndb''))
           (notDistribOut {datoidRel a x y} nxy nxb'')
           (\{y'} ny'b -> notDistribOut (fst (notDistribIn ny'b))
                                        (nmPres (snd (notDistribIn ny'b))))

      lookup2
        :  {a : Datoid}
        -> (x : El a)
        -> (b : El (Bag a))
        -> LookupResult a x b
      lookup2 x (bt nil nd) = lr zero (bt nil nd) (not id) (\{_} _ -> not id)
      lookup2 {a} x (bt (pair n y :: b) (pair nyb ndb)) =
        lookup1 n y (bt b ndb) nyb x
                (decRel (datoidEq a) x y)
                (lookup2 x (bt b ndb))

      lookup3 :  {a : Datoid} -> {x : El a} -> {b : El (Bag a)}
              -> LookupResult a x b -> Pair Nat (El (Bag a))
      lookup3 (lr n b _ _) = pair n b

    lookup : {a : Datoid} -> El a -> El (Bag a) -> Pair Nat (El (Bag a))
    lookup x b = lookup3 (lookup2 x b)

    private
      insert' :  {a : Datoid} -> (x : El a) -> {b : El (Bag a)}
              -> LookupResult a x b -> El (Bag a)
      insert' x (lr n (bt b ndb) nxb _) =
        bt (pair (Pos.suc' n) x :: b) (pair nxb ndb)

    insert : {a : Datoid} -> El a -> El (Bag a) -> El (Bag a)
    insert x b = insert' x (lookup2 x b)

    private

      postulate
        insertLemma1
          :  {a : Datoid}
          -> (x : El a)
          -> (b : El (Bag a))
          -> (nxb : Not (member a x (contents b)))
          -> datoidRel (Bag a)
                       (insert x b)
                       (bt (pair Pos.one x :: list b) (pair nxb (invariant b)))

        insertLemma2
          :  {a : Datoid}
          -> (n : Pos.Pos)
          -> (x : El a)
          -> (b : El (Bag a))
          -> (nxb : Not (member a x (contents b)))
          -> datoidRel (Bag a)
                       (insert x (bt (pair n x :: list b)
                                     (pair nxb (invariant b))))
                       (bt (pair (Pos.suc n) x :: list b)
                           (pair nxb (invariant b)))

  ----------------------------------------------------------------------
  -- Bag traversals

  data Traverse (a : Datoid) : Set where
    Empty  : Traverse a
    Insert : (x : El a) -> (b : El (Bag a)) -> Traverse a

  run : {a : Datoid} -> Traverse a -> El (Bag a)
  run Empty        = empty
  run (Insert x b) = insert x b

  abstract

    traverse : {a : Datoid} -> El (Bag a) -> Traverse a
    traverse     (bt nil _)                          = Empty
    traverse {a} (bt (pair n x :: b) (pair nxb ndb)) = traverse' (Pos.pred n)
      where
      private
        traverse' :  Maybe Pos.Pos -> Traverse a
        traverse' Nothing  = Insert x (bt b ndb)
        traverse' (Just n) = Insert x (bt (pair n x :: b) (pair nxb ndb))

    traverseTraverses
      :  {a : Datoid} -> (b : El (Bag a))
      -> datoidRel (Bag a) (run (traverse b)) b
    traverseTraverses {a} (bt nil unit) = dRefl (Bag a) {empty}
    traverseTraverses {a} (bt (pair n x :: b) (pair nxb ndb)) =
      tT (Pos.pred n) (Pos.predOK n)
      where
      private
        postulate
          subst' :  {a : Datoid} -> (P : El a -> Set) -> (x, y : El a)
                 -> datoidRel a x y -> P x -> P y

        tT :  (predN : Maybe Pos.Pos)
           -> Pos.Pred n predN
           -> datoidRel (Bag a)
                        (run (traverse (bt (pair n x :: b) (pair nxb ndb))))
                        (bt (pair n x :: b) (pair nxb ndb))
        tT Nothing  (Pos.ok eq) = ?
          -- subst' (\p -> datoidRel (Bag a)
          --                 (run (traverse (bt (pair p x :: b) (pair nxb ndb))))
          --                 (bt (pair p x :: b) (pair nxb ndb)))
          --        Pos.one n eq (insertLemma1 x (bt b ndb) nxb)

          -- eq : one == n
          -- data Pred (p : Pos) (mP : Maybe Pos) : Set where
          --   ok : datoidRel posDatoid (sucPred mP) p -> Pred p mP
          -- insert x (bt b ndb) == bt (pair n x :: b) (pair nxb ndb)
        tT (Just n) (Pos.ok eq) = ? -- insertLemma2 n x (bt b ndb) nxb
          -- insert x (bt (pair n x :: b) (pair nxb btb) ==
          -- bt (pair (suc n) x :: b) (pair nxb btb)

    bagElim
      :  {a : Datoid}
      -> (P : El (Bag a) -> Set)
      -> Respects (Bag a) P
      -> P empty
      -> ((x : El a) -> (b : El (Bag a)) -> P b -> P (insert x b))
      -> (b : El (Bag a))
      -> P b
    bagElim {a} P Prespects e i b =
      bagElim' b (traverse b) (traverseTraverses b)
      where
      private
        bagElim'
          :  (b : El (Bag a))
          -> (t : Traverse a)
          -> datoidRel (Bag a) (run t) b
          -> P b
        bagElim' b Empty         eq = subst Prespects empty b eq e
        bagElim' b (Insert x b') eq =
          subst Prespects (insert x b') b eq
                (i x b' (bagElim' b' (traverse b') (traverseTraverses b')))

  ----------------------------------------------------------------------
  -- Respect and equality preservation lemmas

    postulate
      insertPreservesRespect
        :  {a : Datoid}
        -> (P : El (Bag a) -> Set)
        -> (x : El a)
        -> Respects (Bag a) P
        -> Respects (Bag a) (\b -> P (insert x b))

      lookupPreservesRespect
        :  {a : Datoid}
        -> (P : El (Bag a) -> Set)
        -> (x : El a)
        -> Respects (Bag a) P
        -> Respects (Bag a) (\b -> P (snd $ lookup x b))

      -- This doesn't type check without John Major equality or some
      -- ugly substitutions...
      -- bagElimPreservesEquality
      --   :  {a : Datoid}
      --   -> (P : El (Bag a) -> Set)
      --   -> (r : Respects (Bag a) P)
      --   -> (e : P empty)
      --   -> (i : (x : El a) -> (b : El (Bag a)) -> P b -> P (insert x b))
      --   -> (   (x1, x2 : El a) -> (b1, b2 : El (Bag a))
      --       -> (p1 : P b1) -> (p2 : P b2)
      --       -> (eqX : datoidRel a x1 x2) -> (eqB : datoidRel (Bag a) b1 b2)
      --       -> i x1 b1 p1 =^= i x2 b2 p2
      --      )
      --   -> (b1, b2 : El (Bag a))
      --   -> datoidRel (Bag a) b1 b2
      --   -> bagElim P r e i b1 =^= bagElim P r e i b2
