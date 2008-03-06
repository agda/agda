module Loc (K : Set) where

open import Basics
open import Pr
open import Nom

data Loc : Set where
  EL : Loc
  _*_ : Loc -> K -> Loc

infixl 50 _*_

data _!_ : Loc -> K -> Set where
  top : {L : Loc}{S : K} -> (L * S) ! S
  pop : {L : Loc}{S T : K} -> L ! S -> (L * T) ! S

_<*_ : K -> Loc -> Loc
S <* EL = EL * S
S <* (L * T) = (S <* L) * T

max : {S : K}(L : Loc) -> (S <* L) ! S
max EL = top
max (L * T) = pop (max L)

_<_ : (S : K){L : Loc}{T : K} -> L ! T -> (S <* L) ! T
S < top = top
S < pop x = pop (S < x)

data MaxV (S : K)(L : Loc) : {T : K} -> (S <* L) ! T -> Set where
  isMax : MaxV S L (max L)
  isLow : {T : K}(x : L ! T) -> MaxV S L (S < x)

maxV : (S : K)(L : Loc){T : K}(x : (S <* L) ! T) -> MaxV S L x
maxV S EL top = isMax
maxV S EL (pop ())
maxV S (L * T) top = isLow top
maxV S (L * T) (pop x) with maxV S L x
maxV S (L * T) (pop .(max L)) | isMax = isMax
maxV S (L * T) (pop .(S < x)) | isLow x = isLow (pop x)

_bar_ : (L : Loc){S : K} -> L ! S -> Loc
EL bar ()
(L * S) bar top = L
(L * S) bar (pop v) = (L bar v) * S

infixl 50 _bar_

_thin_ : {L : Loc}{S T : K}(x : L ! S) -> (L bar x) ! T -> L ! T
top thin y = pop y
(pop x) thin top = top
(pop x) thin (pop y) = pop (x thin y)

data VarQV {L : Loc}{S : K}(x : L ! S) : {T : K} -> (L ! T) -> Set where
  vSame : VarQV x x
  vDiff : {T : K}(y : (L bar x) ! T) -> VarQV x (x thin y)

varQV : {L : Loc}{S T : K}(x : L ! S)(y : L ! T) -> VarQV x y
varQV top top = vSame
varQV top (pop y) = vDiff y
varQV (pop x) top = vDiff top
varQV (pop x) (pop y) with varQV x y
varQV (pop x) (pop .x) | vSame = vSame
varQV (pop x) (pop .(x thin y)) | vDiff y = vDiff (pop y)
