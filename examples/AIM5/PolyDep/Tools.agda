module Tools where
import PolyDepPrelude
-- import Sigma
-- import And

open PolyDepPrelude  using(Datoid;  Bool; true; false; _&&_; Nat;  True;  Taut; unit)

liftAnd : (a : Bool)(b : Bool)(ta : True a)(tb : True b) -> True (a && b)
liftAnd (true)  (true)  ta tb = unit
liftAnd (true)  (false) ta () -- empty
liftAnd (false) _       () _  -- empty

{-
sigmaCond (D:Datoid)
          (B:D.Elem -> Set)
          (C:Set)
          (ifTrue:(b:D.Elem) -> B b -> B b -> C)
          (ifFalse:C)
          (x:Sigma D.Elem B)
          (y:Sigma D.Elem B)
  : C
  = case x of {
      (si a pa) ->
        case y of {
          (si b pb) ->
            let caseOn (e:Bool)(cast:True e -> B a -> B b) : C
                  = case e of {
                      (false) -> ifFalse;
                      (true) -> ifTrue b (cast tt@_ pa) pb;}
            in  caseOn (D.eq a b) (D.subst B);};}
-- trueAnd = \a b -> (LogicBool.spec_and a b).snd
trueAnd (a:Bool)(b:Bool)(p:And (True a) (True b)) : True (a && b)
  = case p of {
      (Pair a' b') ->
        case a of {
          (true) ->
            case b of {
              (true) -> tt@_;
              (false) -> b';};
          (false) -> a';};}
splitAnd (a:Bool)(b:Bool)(p:True (_&&_ a b))
  : Times (True a) (True b)
  = case a of {
      (true) ->
        case b of {
          (true) ->
            struct {
              fst = tt@_;
              snd = tt@_;};
          (false) -> case p of { };};
      (false) -> case p of { };}
trueSigma (D:Set)(f:D -> Bool)(s:Sigma D (\(d:D) -> True (f d)))
  : True (f (si1 D (\(d:D) -> True (f d)) s))
  = case s of { (si a b) -> b;}
Maybe (A:Set) : Set
  = data Nothing | Just (a:A)
mapMaybe (|A,|B:Set)(f:A -> B)(x:Maybe A) : Maybe B
  = case x of {
      (Nothing) -> Nothing@_;
      (Just a)  -> Just@_ (f a);}
maybe (|A,|B:Set)(e:B)(f:A -> B) : Maybe A -> B
  = \x -> case x of {
            (Nothing) -> e;
            (Just a) -> f a;}
open SET
 use  List,  Absurd,  Unit,  Either,  mapEither,  Times,  mapTimes,  id,
      uncur,  elimEither
elimList (|A:Set)
         (C:List A -> Type)
         (n:C nil@_)
         (c:(a:A) -> (as:List A) -> C as -> C (con@_ a as))
         (as:List A)
  : C as
  = case as of {
      (nil) -> n;
      (con x xs) -> c x xs (elimList C n c xs);}
-- Common generalization of sum and product of a list of sets
--   (represented as a decoding function f and a list of codes)
O (A:Set)(E:Set)(Op:Set -> Set -> Set)(f:A -> Set)
  : List A -> Set
  = elimList (\as -> Set) E (\a -> \as -> Op (f a))
-- The corresponding map function! (Takes a nullary and a binary
-- functor as arguments.)
mapO (|A,|E:Set)
     (|Op:Set -> Set -> Set)
     (mapE:E -> E)
     (mapOp:(A1,B1,A2,B2:Set) |->
             (f1:A1 -> B1) ->
             (f2:A2 -> B2) ->
             Op A1 A2 -> Op B1 B2)
     (X:A -> Set)
     (Y:A -> Set)
     (f:(a:A) -> X a -> Y a)
  : (as:List A) -> O A E Op X as -> O A E Op Y as
  = elimList (\(as:List A) -> O A E Op X as -> O A E Op Y as) mapE
      (\a -> \as -> mapOp (f a))
mapAbsurd : Absurd -> Absurd = id
eqAbsurd  : Absurd -> Absurd -> Bool = \h -> \h' -> case h of { }
-- the name of OPlus and OTimes indicate the symbols they should be
--   shown as in algebra: a big ring (a big "O") with the operator +
--   or x in
-- Disjoint sum over a list of codes
OPlus (A:Set) : (A -> Set) -> List A -> Set
  = O A Absurd Either
-- corresponding map function
mapOPlus (|A:Set)(X:A -> Set)(Y:A -> Set)(f:(a:A) -> X a -> Y a)
  : (as:List A) -> OPlus A X as -> OPlus A Y as
  = mapO id mapEither X Y f
-- Cartesian product over a list of codes
OTimes (A:Set) : (A -> Set) -> List A -> Set
  = O A Unit Times
-- corresponding map
mapOTimes (|A:Set)(X:A -> Set)(Y:A -> Set)(f:(a:A) -> X a -> Y a)
  : (as:List A) -> OTimes A X as -> OTimes A Y as
  = mapO id mapTimes X Y f
sizeOPlus (|A:Set)
          (f:A -> Set)
          (n:(a:A) -> f a -> Nat)
          (as:List A)
          (t:OPlus A f as)
  : Nat
  = case as of {
      (nil) -> case t of { };
      (con a as) ->
        case t of {
          (inl x) -> n a x;
          (inr y) -> sizeOPlus f n as y;};}
triv (x:Absurd)  : Set  = case x of { }
trivT (x:Absurd) : Type = case x of { }
sizeOTimes (|A:Set)
           (f:A -> Set)
           (z:Nat)
           (n:(a:A) -> f a -> Nat)
           (as:List A)
           (t:OTimes A f as)
  : Nat
  = case as of {
      (nil)      -> case t of { (tt) -> z;};
      (con a as) -> uncur (+) (mapTimes (n a) (sizeOTimes f z n as) t);}
eqUnit (x:Unit)(y:Unit) : Bool
  = true@_
eqTimes (|A1,|A2,|B1,|B2:Set)
        (eq1:A1 -> B1 -> Bool)
        (eq2:A2 -> B2 -> Bool)
  : Times A1 A2 -> Times B1 B2 -> Bool
  = \x -> \y -> _&&_ (eq1 x.fst y.fst) (eq2 x.snd y.snd)
EqFam (A:Set)(f:A -> Set)(g:A -> Set) : Set
  = (a:A) -> f a -> g a -> Bool
eqOTimes (A:Set)(f:A -> Set)(g:A -> Set)(eq:EqFam A f g)
  : EqFam (List A) (OTimes A f) (OTimes A g)
  = elimList
      (\as ->  (OTimes A f as -> OTimes A g as -> Bool))
      eqUnit
      (\a -> \as -> eqTimes (eq a))
eqEither (|A1,|A2,|B1,|B2:Set)
       (eq1:A1 -> B1 -> Bool)
       (eq2:A2 -> B2 -> Bool)
  : Either A1 A2 -> Either B1 B2 -> Bool
  = \x -> \y ->
            case x of {
              (inl x') ->
                case y of {
                  (inl x0) -> eq1 x' x0;
                  (inr y') -> false@_;};
              (inr y') ->
                case y of {
                  (inl x') -> false@_;
                  (inr y0) -> eq2 y' y0;};}
eqOPlus (A:Set)(f:A -> Set)(g:A -> Set)(eq:EqFam A f g)
  : EqFam (List A) (OPlus A f) (OPlus A g)
  = elimList
      (\(as:List A) -> OPlus A f as -> OPlus A g as -> Bool)
      eqAbsurd
      (\a -> \as -> eqEither (eq a))
Fam (I:Set)(X:I -> Set) : Type
  = (i:I) -> X i -> Set
eitherSet (A:Set)(B:Set)(f:A -> Set)(g:B -> Set)(x:Either A B)
  : Set
  = case x of {
      (inl x') -> f x';
      (inr y) -> g y;}
famOPlus (A:Set)(G:A -> Set) : Fam A G -> Fam (List A) (OPlus A G)
  = \(f:Fam A G) ->
    elimList (\(as:List A) -> OPlus A G as -> Set) triv
      (\(a:A) -> \(as:List A) -> eitherSet (G a) (OPlus A G as) (f a))
bothSet (A:Set)(B:Set)(f:A -> Set)(g:B -> Set)(x:Times A B)
  : Set
  = Times (f x.fst) (g x.snd)
famOTimes (A:Set)(G:A -> Set)
  : Fam A G -> Fam (List A) (OTimes A G)
  = \(f:Fam A G) ->
    elimList (\(as:List A) -> OTimes A G as -> Set)
      (\(u:OTimes A G nil@_) -> Unit)
      (\(a:A) -> \(as:List A) -> bothSet (G a) (OTimes A G as) (f a))
FAM (I:Set)(X:I -> Set)(Y:(i:I) -> X i -> Set) : Type
  = (i:I) -> (x:X i) -> Y i x
eitherFAM (A:Set)
          (A2:Set)
          (G:A -> Set)
          (G2:A2 -> Set)
          (H:Fam A G)
          (H2:Fam A2 G2)
          (a:A)
          (a2:A2)
          (f:(x:G a) -> H a x)
          (f2:(x2:G2 a2) -> H2 a2 x2)
          (x:Either (G a) (G2 a2))
  : eitherSet (G a) (G2 a2) (H a) (H2 a2) x
  = case x of {
      (inl y) -> f y;
      (inr y2) -> f2 y2;}
FAMOPlus (A:Set)(G:A -> Set)(H:Fam A G)
  : FAM A G H -> FAM (List A) (OPlus A G) (famOPlus A G H)
  = \(f:FAM A G H) ->
    elimList (\(as:List A) -> (x:OPlus A G as) -> famOPlus A G H as x)
      (\(x:OPlus A G nil@_) -> whenZero (famOPlus A G H nil@_ x) x)
      (\(a:A) ->
       \(as:List A) ->
       eitherFAM A (List A) G (OPlus A G) H (famOPlus A G H) a as (f a))
bothFAM (A:Set)
        (A2:Set)
        (G:A -> Set)
        (G2:A2 -> Set)
        (H:Fam A G)
        (H2:Fam A2 G2)
        (a:A)
        (a2:A2)
        (f:(x:G a) -> H a x)
        (f2:(x2:G2 a2) -> H2 a2 x2)
        (x:Times (G a) (G2 a2))
  : bothSet (G a) (G2 a2) (H a) (H2 a2) x
  = struct {
      fst = f x.fst;
      snd = f2 x.snd;}
FAMOTimes (A:Set)(G:A -> Set)(H:Fam A G)
  : FAM A G H -> FAM (List A) (OTimes A G) (famOTimes A G H)
  = \(f:FAM A G H) ->
    elimList
      (\(as:List A) -> (x:OTimes A G as) -> famOTimes A G H as x)
      (\(x:OTimes A G nil@_) -> x)
      (\(a:A) ->
       \(as:List A) ->
       bothFAM A (List A) G (OTimes A G) H (famOTimes A G H) a as (f a))
-}
{-
  Size (A:Set) : Type
    = A -> Nat

  size_OPlus (A:Set)
             (f:A -> Set)
             (size_f:(a:A) -> f a -> Nat)
             (as:List A)
    : OPlus f as -> Nat
    = \(x:OPlus f as) -> ?

  size_OPlus (A:Set)
             (f:A -> Set)
             (size_f:(a:A) -> Size (f a))
             (as:List A)
    : Size (OPlus f as)
    = \(x:OPlus f as) ->
-}
{- Alfa unfoldgoals off
brief on
hidetypeannots off
wide

nd
hiding on
var "mapMaybe" hide 2
var "sigmaCond" hide 3
var "maybe" hide 2
var "O" hide 1
var "OTimes" hide 1
var "OPlus" hide 1
var "mapOPlus" hide 3
var "id" hide 1
var "mapOTimes" hide 3
var "mapO" hide 3
var "mapOp" hide 4
var "uncur" hide 3
var "mapTimes" hide 4
var "sizeOTimes" hide 2
var "sizeOPlus" hide 2
var "eqTimes" hide 4
var "OTimesEq" hide 3
var "elimList" hide 1
var "eqOTimes" hide 3
var "eqEither" hide 4
var "eqOPlus" hide 3
var "eitherSet" hide 2
var "bothSet" hide 2
var "famOPlus" hide 2
var "famOTimes" hide 2
var "helper4" hide 4
var "eitherFAM" hide 4
var "FAMOTimes" hide 3
var "FAMOPlus" hide 3
 #-}
