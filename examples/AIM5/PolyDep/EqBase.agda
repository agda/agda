module EqBase where
import PolyDepPrelude
open PolyDepPrelude using
  ( Bool; true; false; _&&_
  ; Unit; unit
  ; Pair; pair
  ; Either; left; right
  ; Absurd
  ; Datoid; datoid; pElem
  ; True )

-- import And
And = Pair

-- import Sigma
data Sigma (A : Set)(B : A -> Set) : Set where
  si : (a : A) -> (b : B a) -> Sigma A B

Eq : Set -> Set -> Set
Eq a b = a -> b -> Bool

eqEmpty : Eq Absurd Absurd
eqEmpty () -- empty


eqUnit : Eq Unit Unit
eqUnit unit unit = true

eqPair : {A1 A2 B1 B2 : Set} ->
         (Eq     A1          A2) ->
         (Eq        B1          B2) ->
         Eq (And A1 B1) (And A2 B2)
eqPair ea eb (pair a b) (pair a' b') = ea a a' && eb b b'

caseOn : (D : Datoid)
         {B1 B2 : pElem D -> Set}
         (ifTrue : (b : pElem D) -> B1 b -> B2 b -> Bool)
         (a b : pElem D)
         (pa : B1 a)
         (pb : B2 b)
         (e : Bool)
         (cast : True e -> B1 a -> B1 b)
         -> Bool
caseOn D ifTrue a b pa pb (false) cast = false
caseOn D ifTrue a b pa pb (true)  cast = ifTrue b (cast unit pa) pb

eqEither : {A1 A2 B1 B2 : Set}
           (eq1 : A1 -> B1 -> Bool)
           (eq2 : A2 -> B2 -> Bool)
         -> Either A1 A2 -> Either B1 B2 -> Bool
eqEither eq1 eq2 (left  a1) (left  b1) = eq1 a1 b1
eqEither eq1 eq2 (right a2) (right b2) = eq2 a2 b2
eqEither eq1 eq2 _          _          = false

{-
            case x of {
              (inl x') ->
                case y of {
                  (inl x0) -> eq1 x' x0;
                  (inr y') -> false@_;};
              (inr y') ->
                case y of {
                  (inl x') -> false@_;
                  (inr y0) -> eq2 y' y0;};}
-}
{-

eqSigma2 (D : Datoid)
         (|B1 |B2 : pElem D -> Set)
         (ifTrue : (b : pElem D) -> Eq (B1 b) (B2 b))
         (x : Sigma pElem D B1)
         (y : Sigma pElem D B2)
  : Bool
  = case x of {
      (si a pa) ->
        case y of {
          (si b pb) ->
            caseOn D ifTrue a b pa pb (D.eq a b) (D.subst B1);};}

eqSigma (D : Datoid)(|B1 : (a : pElem D) -> Set)(|B2 : (a : pElem D) -> Set)
  : ((a : pElem D) -> Eq (B1 a) (B2 a)) ->
     Eq (Sigma pElem D B1) (Sigma pElem D B2)
  = eqSigma2 D
-- More readable but less useful definition of eqSigma : 

eqSigmaLocalLet (D : Datoid)
                (|B1 |B2 : pElem D -> Set)
                (ifTrue : (b : pElem D) -> Eq (B1 b) (B2 b))
                (x : Sigma pElem D B1)
                (y : Sigma pElem D B2)
  : Bool
  = case x of {
      (si a pa) ->
        case y of {
          (si b pb) ->
            let caseOn (e : Bool)(cast : True e -> B1 a -> B1 b) : Bool
                  = case e of {
                      (false) -> false@_;
                      (true) -> ifTrue b (cast tt@_ pa) pb;}
            in  caseOn (D.eq a b) (D.subst B1);};}


eqSum' (D : Datoid)
     (|B1 |B2 : (a : pElem D) -> Set)
  : ((a : pElem D) -> Eq (B1 a) (B2 a)) ->
     Eq (Sum pElem D B1) (Sum pElem D B2)
  = \(e : (a : pElem D) -> Eq (B1 a) (B2 a)) ->
    \(p1 : Sum pElem D B1) ->
    \(p2 : Sum pElem D B2) ->
    caseOn D e p1.fst p2.fst p1.snd p2.snd (D.eq p1.fst p2.fst)
      (D.subst B1)


eqSum : (D : Datoid)
        {B1 B2 : (a : pElem D) -> Set}
  -> ((a : pElem D) -> Eq (B1 a) (B2 a)) ->
     Eq (Sum pElem D B1) (Sum pElem D B2)
eqSum e p1 p2 =
    caseOn D e p1.fst p2.fst p1.snd p2.snd (D.eq p1.fst p2.fst)
      (D.subst B1)
-}
