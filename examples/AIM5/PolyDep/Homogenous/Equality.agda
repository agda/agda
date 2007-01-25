-- -----------------------------
-- Equality

module Homogenous.Equality where
import Homogenous.Base
import EqBase
import Prelude

open Prelude using ( Datoid
                   ; Bool; true; false; _&&_
                   ; Pair; pair
                   ; Either; left; right
                   ; suc
                   ; _::_; nil
                   ; cmp
                   ; _=>_; lam; _$$_)
open Homogenous.Base using (Arity; Sig; Fa; F; T; It; out)

eq_step_ar : (n:Arity){X:Set}(fs:Fa n (X => Bool))(xs:Fa n X) -> Bool
eq_step_ar (zer)   unit         unit         = true
eq_step_ar (suc m) (pair f fs') (pair x xs') = f $$ x && eq_step_ar m fs' xs'

-- We write left as This (as in "This constructor" and right as Other
-- (as in "one of the Other constructors") to help the reader

eq_step' : (fi:Sig){X:Set} -> F fi (X => Bool) -> F fi X -> Bool
eq_step' (nil)   ()         ()  -- empty
eq_step' (n::ns) (left fs ) (left xs ) = eq_step_ar n fs xs
eq_step' (n::ns) (left fs ) (right y') = false
eq_step' (n::ns) (right x') (left xs ) = false
eq_step' (n::ns) (right x') (right y') = eq_step' ns x' y'

eq_step : (fi:Sig)(x:F fi (T fi => Bool)) -> T fi => Bool
eq_step fi x = lam ( \t -> eq_step' fi x (out fi t) )

equal' : (fi:Sig) -> T fi -> (T fi => Bool)
equal' fi = It fi (eq_step fi)

equal : (fi:Sig) -> T fi -> T fi -> Bool
equal fi x y = equal' fi x $$ y

{-
module Homogenous_Equality_zip where

open Homogenous_Base use Arity, Sig, Fa, F, T, It, out

public open EqBase use Eq

-- Notation: Equality families for Arity and Sig(nature) levels

EqA (X:Set)(Y:Set) : Set = (n:Arity)-> Eq (Fa n X) (Fa n Y)
EqS (X:Set)(Y:Set) : Set = (fi:Sig) -> Eq (F fi X) (F fi Y)

-- Preliminaries: we need an Arity level Boolean and

andA2 (n:Arity) (bs:Fa n Bool) : Bool
  = case n of
    (zer  )-> true@_
    (suc m)-> and bs.fst (andA2 m bs.snd)

andA (n:Arity) : Fa n Bool -> Bool
  = andA2 n

-- We need zipWith (also on the Arity level)

zipWithA (|X,|Y,|Z:Set)(e:X->Y->Z)
         (n:Arity)(fs: Fa n X) (xs:Fa n Y) : Fa n Z
  = case n of
    (zer  )-> tt@_
    (suc m)-> struct {fst = e fs.fst xs.fst;
                      snd = zipWithA e m fs.snd xs.snd}

-- The two versions of match are identical. We just want to show the
-- simple type (no suffix) and the type necessary for doing case
-- (suffix 2). The definition of match2 would be in a local let if
-- it wasn't for Agda-problems with scopes.

match2 (X:Set)(Y:Set)(f:EqA X Y)(fi:Sig)(fx:F fi X)(fy:F fi Y) : Bool
    = case fi of
      (nil     )-> case fx of { }
      (con n ns)-> case fx of
        (left xa)-> case fy of (left ya)-> f n xa ya
                              (right yb)-> false@_
        (right xb)-> case fy of (left ya)-> false@_
                              (right yb)-> match2 X Y f ns xb yb

-- match is the first main function: lifts a family of euqlity tests
-- on the Arity level to a family on the Sig level.

match (X:Set)(Y:Set) : EqA X Y -> EqS X Y
  = match2 X Y

-- We combine andA with zipWithA to lift an equality test e to the
-- Arity level

andzipWithA (X:Set)(Y:Set) : Eq X Y -> EqA X Y
  = \(e:Eq X Y) -> \(n:Arity)-> \(xs:Fa n X) -> \(ys:Fa n Y) ->
      andA n (zipWithA e n xs ys)

-- Then we compose the two liftings:

matchAndZipWith (X:Set) (Y:Set) : Eq X Y -> EqS X Y
  = cmp (match       X Y) (andzipWithA X Y)

-- Finally we instantiate to id (the more general case is used in
-- the proof of reflexivity)

recogAll (X:Set) : EqS (X->Bool) X
  = matchAndZipWith (X->Bool) X id

--    = match (X->Bool) X (andzipWithApply X)

eq_step (fi:Sig)(x:F fi (T fi -> Bool)) : T fi -> Bool
  = cmp (recogAll (T fi) fi x)
        (out fi)

equal (fi:Sig) : T fi -> (T fi -> Bool)
  = It fi (eq_step fi)


-- Unused code below

zipWithApply (X:Set)(Y:Set)(n:Arity) : Fa n (X->Y) -> (Fa n X -> Fa n Y)
  = zipWithA id n

andzipWithApply (X:Set)(n:Arity)(fs: Fa n (X-> Bool)) (xs: Fa n X) : Bool
  = andA n (zipWithApply X Bool n fs xs)
-}
