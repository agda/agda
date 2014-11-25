-- Andreas, 2014-11-25, issue reported by Peter Divianski (divipp)

{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc:10 #-}
-- {-# OPTIONS -v tc.inj:49 #-}
-- {-# OPTIONS -v tc.polarity:49 #-}
-- {-# OPTIONS -v tc.lhs:40 #-}

-- After loading the following Agda code, the last occurrence of 'one' is yellow.

-- Remarks:
-- Probably not an error, but it is against my expectation.
-- The code was obtained by shrinking a more complex one.
-- I guess that the lifting of the local function 'f' happens not as I expect it.
-- The code is quite fragile, the any of following changes fix the problem:
-- - using record ⊤ instead of data Unit
-- - lifting 'f' to be a global function
-- - replacing 'unit' by '_' in the definition of 'f'
-- - giving the implicit argument {v = unit ∷ []} to g

-- Tested with Agda 2.4.2.1 and with the development version of Agda on GitHub (20 Nov 2014)

open import Common.Prelude using (Nat; zero; suc; Unit; unit)

data Vec (A : Set) : Nat → Set where
   []  : Vec A zero
   _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)  -- n is forced

-- Singleton type
data Sg {A : Set} (x : A) : Set where
  sg : Sg x

-- modified length function (counts till 1)
nonNil : ∀ {n} → Vec Unit n → Nat
nonNil []       = zero
nonNil (i ∷ is) = suc (f i) where
  f : Unit → Nat
  f unit = zero

g : ∀ {n} {v : Vec Unit n} → Sg (nonNil v) → Sg v
g sg = sg

one : Sg (suc zero)
one = sg

test : Sg (unit ∷ [])
test = g one    -- `one' is yellow, a meta coming from the forced n

{- Analysis

g :=> Sg (nonNil {_n} _v) -> Sg _v
one :=> Sg (suc zero)
suc zero =?= nonNil {_n} _v
use injectivity
_n := suc _n'
_v := _∷_ {_nv} _i _is
zero =?= f {_nv} {_i} {_is} _i
using injectivity on f creates unsolved, because "forced" meta:

inverting injective function _.f :
({.n : Nat} (i : Unit) (is : Vec Unit .n) → Unit → Nat) for zero
(args = [$ {_32}, $ _33, $ _34, $ _33])
meta patterns [_35, _36, _37]
  perm = x0,x1,x2 -> x0,x1,x2
  tel  = {.n : Nat} (i : Unit) (is : Vec Unit .n)
  ps   = [[]!{VarP ".n"}, []k(VarP "i"), []k(VarP "is"),
          []r(ConP Common.Prelude.Unit.unit(inductive)[] Nothing [])]
inversion
  lhs  = [$ {_35}, $ _36, $ _37, $ unit]
  rhs  = [$ {_32}, $ _33, $ _34, $ _33]
  type = ({.n : Nat} (i : Unit) (is : Vec Unit .n) → Unit → Nat)
  a    = ({.n : Nat} (i : Unit) (is : Vec Unit .n) → Unit → Nat)
  v    = (_.f)
  arg1 = {_35}
  arg2 = {_32}
-- Here, the equality check is skipped as n is "forced", so the
-- assignment _35 := _32 does not happen
  a    = ((i : Unit) (is : Vec Unit _35) → Unit → Nat)
  v    = (_.f {_35})
  arg1 = _36
  arg2 = _33
term _36 := _33
term _36 := _33
solving _36 := _33
  a    = ((is : Vec Unit _35) → Unit → Nat)
  v    = (_.f {_35} _33)
  arg1 = _37
  arg2 = _34
term _37 := _34
term _37 := _34
solving _37 := _34
  a    = (Unit → Nat)
  v    = (_.f {_35} _33 _34)
  arg1 = unit
  arg2 = _33
compareTerm unit == _33 : Unit
term _33 := unit
term _33 := unit
solving _33 := unit
compareTerm zero == (_.f {_32} unit _34 unit) : Nat
-}

-- Should work without unsolved metas.
