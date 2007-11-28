{-# OPTIONS --allow-unsolved-metas --no-termination-check
  #-}
module Bag where

  import Prelude
  import Equiv
  import Datoid
  import Eq
  import Nat
  import List
  import Pos

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
      -- If this were Coq then the invariant should be a Prop. Similar
      -- remarks apply to some definitions below. Since I have to write
      -- the supporting library myself I can't be bothered to
      -- distinguish Set and Prop right now though.

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

      eqSym :  {a : Datoid} -> (x y : BagType a)
            -> BagEq a x y -> BagEq a y x
      eqSym {a} x y = sym (Permutation (elemDatoid a)) {list x} {list y}

      eqTrans :  {a : Datoid} -> (x y z : BagType a)
            -> BagEq a x y -> BagEq a y z -> BagEq a x z
      eqTrans {a} x y z = trans (Permutation (elemDatoid a))
                                {list x} {list y} {list z}

      eqDec : {a : Datoid} -> (x y : BagType a)
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
          subst' :  {a : Datoid} -> (P : El a -> Set) -> (x y : El a)
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
      --   -> (   (x1 x2 : El a) -> (b1 b2 : El (Bag a))
      --       -> (p1 : P b1) -> (p2 : P b2)
      --       -> (eqX : datoidRel a x1 x2) -> (eqB : datoidRel (Bag a) b1 b2)
      --       -> i x1 b1 p1 =^= i x2 b2 p2
      --      )
      --   -> (b1 b2 : El (Bag a))
      --   -> datoidRel (Bag a) b1 b2
      --   -> bagElim P r e i b1 =^= bagElim P r e i b2
