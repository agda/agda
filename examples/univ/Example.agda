
module Example where

open import Base
open import Nat
open import univ

-- Application

_#_ : {A : S}{F : El A -> S}{pF : Map _==_ _=S_ F} ->
      El (pi A F pF) -> (x : El A) -> El (F x)
el < f , pf > # x = f x

-- Projection

π₀ : {A : S}{F : El A -> S}{pF : Map _==_ _=S_ F} ->
     El (sigma A F pF) -> El A
π₀ (el < x , Fx >) = x

π₁ : {A : S}{F : El A -> S}{pF : Map _==_ _=S_ F} ->
     (p : El (sigma A F pF)) -> El (F (π₀ p))
π₁ (el < x , Fx >) = Fx

