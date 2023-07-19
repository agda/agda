-- Source: https://raw.githubusercontent.com/gallais/potpourri/master/agda/poc/dimensions/dimensions.agda
-- Author: Original by gallais, modified for test suite by P. Hausmann
-- (Later edited by others.)

{-# OPTIONS --guardedness #-}

module dimensions where

open import Data.Nat     as ℕ using (ℕ; NonZero)
open import Data.Nat.LCM
open import Data.Nat.DivMod hiding (_/_)
open import Data.Integer as ℤ using (ℤ ; +_)

open import Data.Unit.Polymorphic using (⊤)
open import Function
open import Relation.Nullary.Decidable

------------------------------------------------
-- DIMENSIONS
-- record { kilogram = x ; meter = y ; second = z }
-- corresponds to the dimension: kg^x * m^y * s^z

module Dimension where

  record dimension : Set where
    field
      kilogram : ℤ
      meter    : ℤ
      second   : ℤ
  open dimension public

  _*_ : (d e : dimension) → dimension
  d * e = record { kilogram = kilogram d ℤ.+ kilogram e
                 ; meter    = meter d    ℤ.+ meter e
                 ; second   = second d   ℤ.+ second e }


  _/_ : (d e : dimension) → dimension
  d / e = record { kilogram = kilogram d ℤ.- kilogram e
                 ; meter    = meter d    ℤ.- meter e
                 ; second   = second d   ℤ.- second e }

open Dimension using (dimension ; kilogram ; meter ; second)

kgram met sec : dimension
kgram = record { kilogram = + 1
               ; meter    = + 0
               ; second   = + 0 }
met   = record { kilogram = + 0
               ; meter    = + 1
               ; second   = + 0 }
sec   = record { kilogram = + 0
               ; meter    = + 0
               ; second   = + 1 }

≠0-mult :
  (m n : ℕ) (hm : NonZero m) (hn : NonZero n) → NonZero (m ℕ.* n)
≠0-mult ℕ.zero    n         () hn
≠0-mult m         0         hm ()
≠0-mult (ℕ.suc m) (ℕ.suc n) hm hn = _


------------------------------------------------
-- UNITS
-- A unit is a dimension together with a coefficient
-- 60 , _ # sec represents a minute (60 seconds)

module Unit where

  infix 1 _,_#_

  data unit : Set where
    _,_#_ : (n : ℕ) (hn : NonZero n) (d : dimension) → unit

  coeff : (u : unit) → ℕ
  coeff (k , _ # _) = k

  coeff≠0 : (u : unit) → NonZero (coeff u)
  coeff≠0 (k , hk # _) = hk

  _*_ : (u v : unit) → unit
  (k , hk # d) * (l , hl # e) =
    ( k ℕ.* l ) , (≠0-mult k l hk hl) # (d Dimension.* e)

  _/_ : (u v : unit)
        ⦃ ≠0 : NonZero (((coeff u) div (coeff v)) ⦃ coeff≠0 v ⦄) ⦄ →
        unit
  _/_ (k , hk # d) (l , hl # e) ⦃ ≠0 ⦄ =
    (k div l) ⦃ hl ⦄ , ≠0 # (d Dimension./ e)

open Unit using (unit ; _,_#_ ; coeff ; coeff≠0)


------------------------------------------------
-- VALUES
-- Finally, values are natural numbers repackaged
-- with a unit

module Values where

  data [_] : (d : unit) → Set where
    ⟨_∶_⟩ : (value : ℕ) (d : unit) → [ d ]

  val : ∀ {d} → [ d ] → ℕ
  val ⟨ m ∶ _ ⟩ = m

  infix 3 _+_
  infix 4 _*_ _/_

  _+_ : ∀ {k hk l hl m hm} {d : dimension} (v₁ : [ k , hk # d ])
        (v₂ : [ l , hl # d ]) → [ m , hm # d ]
  _+_ {k} {hk} {l} {hl} {m} {hm} ⟨ v₁ ∶ ._ ⟩ ⟨ v₂ ∶ ._ ⟩ =
      ⟨ ((k ℕ.* v₁ ℕ.+ l ℕ.* v₂) div m) ⦃ hm ⦄ ∶ _ ⟩

  _:+_ : ∀ {k hk l hl} {d : dimension} (v₁ : [ k , hk # d ])
         (v₂ : [ l , hl # d ]) → [ 1 , _ # d ]
  _:+_ = _+_

  _*_ : ∀ {k hk l hl m hm} {d e : dimension}
        (vd : [ k , hk #  d ]) (ve : [ l , hl # e ]) →
        [ m , hm # (d Dimension.* e) ]
  _*_ {k} {hk} {l} {hl} {m} {hm} ⟨ vd ∶ ._ ⟩ ⟨ ve ∶ ._ ⟩ =
      ⟨ ((k ℕ.* vd ℕ.* l ℕ.* ve) div m) ⦃ hm ⦄ ∶ _ ⟩

  _:*_ : ∀ {k hk l hl} {d e : dimension}
         (vd : [ k , hk #  d ]) (ve : [ l , hl # e ]) →
         [ 1 , _ # (d Dimension.* e) ]
  _:*_ = _*_

  _/_ :  ∀ {k hk l hl m hm} {d e : dimension}
        (vd : [ k , hk #  d ]) (ve : [ l , hl # e ])
        {≠0 : NonZero (val ve)} → [ m , hm # (d Dimension./ e) ]
  _/_ {k} {hk} {l} {hl} {m} {hm} ⟨ vd ∶ ._ ⟩ ⟨ ve ∶ ._ ⟩ {≠0} =
      ⟨ ((k ℕ.* vd) div (l ℕ.* ve ℕ.* m))
          ⦃ ≠0-mult _ _ (≠0-mult _ _ hl ≠0) hm ⦄ ∶ _ ⟩

  ↑ : ∀ {k hk l hl d} → [ k , hk # d ] → [ l , hl # d ]
  ↑ {k} {hk} {l} {hl} ⟨ v ∶ ._ ⟩ = ⟨ ((k ℕ.* v) div l) ⦃ hl ⦄ ∶ _ ⟩

open Values


------------------------------------------------
-- SI PREFIXES
-- They are simply unit-modifying functions.

infix 5 _**_

_**_ : (k : ℕ) {hk : NonZero k} (d : dimension) → unit
_**_ k {hk} d = k , hk # d

centi : (u : unit) {≠0 : NonZero (coeff u div 100)} → unit
centi (k , hk # d) {≠0} = _ , ≠0 # d
deci : (u : unit) {≠0 : NonZero (coeff u div 10)} → unit
deci  (k , hk # d) {≠0} = _ , ≠0 # d
deca hecto kilo : unit → unit
deca  (k , hk # d) = 10   ℕ.* k , ≠0-mult 10   k _ hk # d
hecto (k , hk # d) = 100  ℕ.* k , ≠0-mult 100  k _ hk # d
kilo  (k , hk # d) = 1000 ℕ.* k , ≠0-mult 1000 k _ hk # d

cst : unit
cst =
  let dcst = record { kilogram = + 0
                    ; meter    = + 0
                    ; second   = + 0 }
  in 1 , _ # dcst

infix 3 κ_

κ_ : (n : ℕ) → [ cst ]
κ n = ⟨ n ∶ cst ⟩


------------------------------------------------
-- EXAMPLES

s min hr : unit
s   = 1         ** sec
min = 60        ** sec
hr  = 60 ℕ.* 60 ** sec

m : unit
m = 1 ** met

1s : [ s ]
1s   = ⟨ 1 ∶ s ⟩
1min : [ min ]
1min = ⟨ 1 ∶ min ⟩

1hr 2hr : [ min ]
1hr = ⟨ 60 ∶ min ⟩
2hr = 1hr + 1hr

1min² : [ s Unit.* s ]
1min² = 1min * 1min

60km : [ kilo m ]
60km = ⟨ 60 ∶ kilo m ⟩

60hm : [ hecto m ]
60hm = ⟨ 60 ∶ hecto m ⟩

60hm/min : [ deca m Unit./ s ]
60hm/min = ⟨ 60 ∶ hecto m ⟩ / ⟨ 1 ∶ min ⟩

acc : unit
acc = m Unit./ (s Unit.* s)

spd : unit
spd = m Unit./ s

------------------------------------------------
-- APPLICATION:
-- free fall of a ball with an initial horizontal speed.

record point : Set where
  field
    accx accy : [ acc ]
    vx vy     : [ spd ]
    x y       : [ m   ]
open point public

g : [ acc ]
g = ⟨ 10 ∶ _ ⟩

newton : ∀ (dt : [ s ]) (p : point) → point
newton dt p =
  record { accx = accx p
         ; accy = accy p + g
         ; vx   = vx p   + (accx p :* dt)
         ; vy   = vy p   + (accy p :* dt)
         ; x    = x p    + (vx p   :* dt)
         ; y    = y p    + (vy p   :* dt) }

------------------------------------------------
-- TRACING

-- the initial condition a point is in
base : point
base = record
         { accx = ⟨ 0  ∶ _ ⟩
         ; accy = ⟨ 0  ∶ _ ⟩
         ; vx   = ⟨ 45 ∶ _ ⟩
         ; vy   = ⟨ 0  ∶ _ ⟩
         ; x    = ⟨ 0  ∶ _ ⟩
         ; y    = ⟨ 0  ∶ _ ⟩ }

-- the consecutive steps of its fall
open import Data.Vec     as V using (Vec)

throw : (n : ℕ) (dt : [ s ]) → point → Vec point (ℕ.suc n)
throw  ℕ.zero   dt p = p V.∷ V.[]
throw (ℕ.suc n) dt p = p V.∷ throw n dt (newton dt p)

-- the display function generating the output
open import Data.String     renaming (_++_ to _+s+_)
open import IO
import IO.Primitive
open import Codata.Musical.Colist
open import Data.Nat.Show as Nat
open import Level using (0ℓ)

printPoint : point → IO {0ℓ} ⊤
printPoint p = putStrLn ((Nat.show (val (x p))) +s+ ";" +s+ Nat.show (val (y p)))

main : IO.Primitive.IO ⊤
main = run (Colist.mapM printPoint (Codata.Musical.Colist.fromList trace) >> pure _)
  where trace = V.toList $ throw 15 ⟨ 1 ∶ s ⟩ base
