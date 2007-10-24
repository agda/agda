-- -----------------------------
-- Equality

module Homogenous.Equality where
import Homogenous.Base
import EqBase
import PolyDepPrelude

open PolyDepPrelude using ( Datoid
                   ; Bool; true; false; _&&_
                   ; Pair; pair
                   ; Either; left; right
                   ; suc; zero
                   ; _::_; nil
                   ; cmp; Unit; unit
                   )
open Homogenous.Base using (Arity; Sig; Fa; F; T; It; out)

eq_step_ar : (n : Arity){X : Set}(fs : Fa n (X -> Bool))(xs : Fa n X) -> Bool
eq_step_ar zero    unit         unit         = true
eq_step_ar (suc m) (pair f fs') (pair x xs') = f x && eq_step_ar m fs' xs'

-- We write left as This (as in "This constructor" and right as Other
-- (as in "one of the Other constructors") to help the reader

eq_step' : (fi : Sig){X : Set} -> F fi (X -> Bool) -> F fi X -> Bool
eq_step' (nil)   ()         ()  -- empty
eq_step' (n :: ns) (left fs ) (left xs ) = eq_step_ar n fs xs
eq_step' (n :: ns) (left fs ) (right y') = false
eq_step' (n :: ns) (right x') (left xs ) = false
eq_step' (n :: ns) (right x') (right y') = eq_step' ns x' y'

eq_step : (fi : Sig)(x : F fi (T fi -> Bool)) -> T fi -> Bool
eq_step fi x = \t -> eq_step' fi x (out fi t)

equal' : (fi : Sig) -> T fi -> (T fi -> Bool)
equal' fi = It fi (eq_step fi)

equal : (fi : Sig) -> T fi -> T fi -> Bool
equal fi x y = equal' fi x y

