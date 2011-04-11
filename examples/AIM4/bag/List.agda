
module List where

  import Prelude
  import Equiv
  import Datoid
  import Nat

  open Prelude
  open Equiv
  open Datoid
  open Nat

  data List (a : Set) : Set where
    nil  : List a
    _::_ : a -> List a -> List a

  map : {a b : Set} -> (a -> b) -> List a -> List b
  map f nil       = nil
  map f (x :: xs) = f x :: map f xs

  member : (a : Datoid) -> El a -> List (El a) -> Set
  member _ x nil       = Absurd
  member a x (y :: ys) = Either (rel' (datoidEq a) x y) (member a x ys)

  memberPreservesEq
    :  {a : Datoid}
    -> {x y : El a}
    -> datoidRel a x y
    -> (zs : List (El a))
    -> member a x zs
    -> member a y zs
  memberPreservesEq     xy nil       abs         = abs
  memberPreservesEq {a} xy (z :: zs) (left xz)   =
    left  (dTrans a (dSym a xy) xz)
  memberPreservesEq {a} xy (z :: zs) (right xzs) =
    right (memberPreservesEq {a} xy zs xzs)

  private
    noCopies' : (a : Datoid) -> (x y : El a) -> Dec (datoidRel a x y) 
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
      -> (x y : El a)
      -> Dec (datoidRel a x y)
      -> (ys delXYs : List (El a))
      -> List (El a)
    delete' _ _ _ (left _)  ys _      = ys
    delete' _ _ _ (right _) _  delXYs = delXYs

  -- Removes first occurrence if any.
  delete : (a : Datoid) -> El a -> List (El a) -> List (El a)
  delete a x nil       = nil
  delete a x (y :: ys) = delete' a x y (datoidDecRel a x y) ys (delete a x ys)

  private
    Perm : (a : Datoid) -> (xs ys : List (El a)) -> Set
    Perm a xs ys = forall z -> datoidRel natDatoid (noCopies a z xs)
                                                   (noCopies a z ys)

    refl' : {a : Datoid} -> (xs : List (El a)) -> Perm a xs xs
    refl' {a} xs = \z -> dRefl natDatoid {noCopies a z xs}

    sym' :  {a : Datoid} -> (xs ys : List (El a))
         -> Perm a xs ys -> Perm a ys xs
    sym' {a} xs ys xy =
      \z -> dSym natDatoid {noCopies a z xs} {noCopies a z ys} (xy z)

    trans' : {a : Datoid} -> (xs ys zs : List (El a))
           -> Perm a xs ys -> Perm a ys zs -> Perm a xs zs
    trans' {a} xs ys zs xy yz =
      \z -> dTrans natDatoid
                   {noCopies a z xs} {noCopies a z ys} {noCopies a z zs}
                   (xy z) (yz z)

    postulate
      dec' : {a : Datoid} -> (xs ys : List (El a))
             -> Either (Perm a xs ys) (Not (Perm a xs ys))

  Permutation : (a : Datoid) -> DecidableEquiv (List (El a))
  Permutation a = decEquiv (equiv (Perm a) (refl' {a}) (sym' {a}) (trans' {a})) (dec (dec' {a}))

