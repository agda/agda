module EqBase where
import Prelude
open Prelude using ( Bool; true; false; _&&_
                   ; Unit; unit
                   ; Pair; pair
                   ; Absurd
                   ; Datoid; datoid; pElem
                   ; True )

-- import And
And = Pair

-- import Sigma
data Sigma (A : Set)(B : A -> Set) : Set where
  si : (a : A) -> (b : B a) -> Sigma A B

{-
si1 (A : Set)(B : A -> Set)(s : Sigma A B) : A
  = case s of { (si a b) -> a;}
-}

-- Eq : Set -> Set -> Set
-- Eq a b = a -> b -> Bool  -- type abbreviation not allowed!

eqEmpty : Absurd -> Absurd -> Bool
eqEmpty () -- empty


eqUnit : Unit -> Unit -> Bool
eqUnit unit unit = true

eqPair : {A1 A2 B1 B2 : Set} ->
         (   A1    ->     A2    -> Bool) ->
         (      B1 ->        B2 -> Bool) ->
         And A1 B1 -> And A2 B2 -> Bool
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

eqSum (D : Datoid)
      (|B1 |B2 : (a : pElem D) -> Set)
  : ((a : pElem D) -> Eq (B1 a) (B2 a)) ->
     Eq (Sum pElem D B1) (Sum pElem D B2)
  = \(e : (a : pElem D) -> Eq (B1 a) (B2 a)) ->
    \(p1 : Sum pElem D B1) ->
    \(p2 : Sum pElem D B2) ->
    caseOn D e p1.fst p2.fst p1.snd p2.snd (D.eq p1.fst p2.fst)
      (D.subst B1)
-}
