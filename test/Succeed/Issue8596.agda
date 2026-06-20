module Issue8596 where

infix 1 _≡_
data _≡_ {A : Set} (a : A) : A -> Set where
    refl : a ≡ a

ap : ∀ {A B : Set} (f : A -> B) {a b : A} -> a ≡ b -> f a ≡ f b
ap f refl = refl

infixr 9 _▪_
_▪_ : ∀ {A : Set} {a1 a2 a3 : A} -> a1 ≡ a2 -> a2 ≡ a3 -> a1 ≡ a3
refl ▪ q = q

record ⊤ : Set where
    constructor tt

data Bit : Set where
    lo hi : Bit

record Semicat : Set1 where
    field
        Obj : Set
        Arr : Obj -> Obj -> Set
        _*_ : ∀ {a1 a2 a3} -> Arr a1 a2 -> Arr a2 a3 -> Arr a1 a3
open Semicat

record Pump (A : Semicat) : Set where
    field pump : ∀ {a1 a2 : A .Obj} -> (A .Arr a1 a2) -> (A .Arr a1 a2)
open Pump

record Pump= {A : Semicat} (F G : Pump A) : Set where
    field pump= : ∀ {a1 a2 : A .Obj} (a12 : A .Arr a1 a2) -> F .pump a12 ≡ G .pump a12
open Pump=

record SemicatWithIdempotentPump : Set1 where
    field
        Carrier : ⊤ -> Semicat
        run : Pump (Carrier tt)
        run-idem : ∀ {_ _ _ _ : ⊤} -> Pump= record{pump = \ x -> run .pump (run .pump x)} run
            -- When callgraph nodes were not stratified by copattern projections,
            -- termination checking would fail so long as run-idem had 2 or 4
            -- spurious ⊤ arguments.
open SemicatWithIdempotentPump

record Portal : Set1 where
    field port : ⊤ -> Bit -> Bit
open Portal

data Chain (P : Portal) (b1 b2 : Bit) : Set where
    cons : (b1 ≡ P .port tt lo) -> Chain P (P .port tt lo) b2 -> Chain P b1 b2

portal : Portal
portal .port _ b = b

SWIP : SemicatWithIdempotentPump
SWIP .Carrier a .Semicat.Obj = Bit
SWIP .Carrier a .Semicat.Arr = Chain portal
SWIP .Carrier a .Semicat._*_ (cons e1 c1) p = cons e1 (SWIP .Carrier a .Semicat._*_ c1 p)
SWIP .run .pump (cons e c) = cons e (SWIP .run .pump c)
SWIP .run-idem .pump= (cons refl c) = ap (cons refl) (SWIP .run-idem .pump= c)
