{-# OPTIONS --no-positivity-check #-}
module IIRDg where

import LF
import DefinitionalEquality
import IIRD

open LF
open DefinitionalEquality
open IIRD

mutual

  data Ug {I : Set}{D : I -> Set1}(γ : OPg I D) : I -> Set where
    introg : (a : Gu γ (Ug γ) (Tg γ)) -> Ug γ (Gi γ (Ug γ) (Tg γ) a)

  Tg : {I : Set}{D : I -> Set1}(γ : OPg I D)(i : I) -> Ug γ i -> D i
  Tg γ .(Gi γ (Ug γ) (Tg γ) a) (introg a) = Gt γ (Ug γ) (Tg γ) a

Arg : {I : Set}{D : I -> Set1}(γ : OPg I D) -> Set
Arg γ = Gu γ (Ug γ) (Tg γ)

index : {I : Set}{D : I -> Set1}(γ : OPg I D) -> Arg γ -> I
index γ a = Gi γ (Ug γ) (Tg γ) a

IH : {I : Set}{D : I -> Set1}(γ : OPg I D)(F : (i : I) -> Ug γ i -> Set1) -> Arg γ -> Set1
IH γ = KIH γ (Ug γ) (Tg γ)

-- Elimination rule
Rg : {I : Set}{D : I -> Set1}(γ : OPg I D)(F : (i : I) -> Ug γ i -> Set1) ->
     (h : (a : Arg γ) -> IH γ F a -> F (index γ a) (introg a)) ->
     (i : I)(u : Ug γ i) -> F i u
Rg γ F h .(index γ a) (introg a) = h a (Kmap γ (Ug γ) (Tg γ) F (Rg γ F h) a)

{-
-- We don't have general IIRDs so we have to postulate Ug/Tg

postulate
  Ug : {I : Set}{D : I -> Set1} -> OPg I D -> I -> Set
  Tg : {I : Set}{D : I -> Set1}(γ : OPg I D)(i : I) -> Ug γ i -> D i

  introg : {I : Set}{D : I -> Set1}(γ : OPg I D)(a : Gu γ (Ug γ) (Tg γ)) ->
           Ug γ (Gi γ (Ug γ) (Tg γ) a)

  Tg-equality : {I : Set}{D : I -> Set1}(γ : OPg I D)(a : Gu γ (Ug γ) (Tg γ)) ->
                Tg γ (Gi γ (Ug γ) (Tg γ) a) (introg γ a) ≡₁ Gt γ (Ug γ) (Tg γ) a

  Rg : {I : Set}{D : I -> Set1}(γ : OPg I D)(F : (i : I) -> Ug γ i -> Set1)
       (h : (a : Gu γ (Ug γ) (Tg γ)) -> KIH γ (Ug γ) (Tg γ) F a -> F (Gi γ (Ug γ) (Tg γ) a) (introg γ a))
       (i : I)(u : Ug γ i) -> F i u

  Rg-equality : {I : Set}{D : I -> Set1}(γ : OPg I D)(F : (i : I) -> Ug γ i -> Set1)
                (h : (a : Gu γ (Ug γ) (Tg γ)) -> KIH γ (Ug γ) (Tg γ) F a -> F (Gi γ (Ug γ) (Tg γ) a) (introg γ a))
                (a : Gu γ (Ug γ) (Tg γ)) ->
                Rg γ F h (Gi γ (Ug γ) (Tg γ) a) (introg γ a)
                ≡₁ h a (Kmap γ (Ug γ) (Tg γ) F (Rg γ F h) a)

-- Helpers

ι★g : {I : Set}(i : I) -> OPg I (\_ -> One')
ι★g i = ι < i | ★' >'

-- Examples

module Martin-Löf-Identity where

  IdOP : {A : Set} -> OPg (A * A) (\_ -> One')
  IdOP {A} = σ A \a -> ι★g < a | a >

  _==_ : {A : Set}(x y : A) -> Set
  x == y = Ug IdOP < x | y >

  refl : {A : Set}(x : A) -> x == x
  refl x = introg IdOP < x | ★ >

  -- We have to work slightly harder than desired since we don't have η for × and One.
  private
    -- F C is just uncurry C but dependent and at high universes.
    F : {A : Set}(C : (x y : A) -> x == y -> Set1)(i : A * A) -> Ug IdOP i -> Set1
    F C < x | y > p = C x y p

    h' : {A : Set}(C : (x y : A) -> x == y -> Set1)
         (h : (x : A) -> C x x (refl x))
         (a : Gu IdOP (Ug IdOP) (Tg IdOP)) -> KIH IdOP (Ug IdOP) (Tg IdOP) (F C) a ->
         F C (Gi IdOP (Ug IdOP) (Tg IdOP) a) (introg IdOP a)
    h' C h < x | ★ > _ = h x

  J : {A : Set}(C : (x y : A) -> x == y -> Set1)
      (h : (x : A) -> C x x (refl x))
      (x y : A)(p : x == y) -> C x y p
  J {A} C h x y p = Rg IdOP (F C) (h' C h) < x | y > p

  J-equality : {A : Set}(C : (x y : A) -> x == y -> Set1)
               (h : (x : A) -> C x x (refl x))(x : A) ->
               J C h x x (refl x) ≡₁ h x
  J-equality {A} C h x = Rg-equality IdOP (F C) (h' C h) < x | ★ >

module Christine-Identity where

  IdOP : {A : Set}(a : A) -> OPg A (\_ -> One')
  IdOP {A} a = ι★g a

  _==_ : {A : Set}(x y : A) -> Set
  x == y = Ug (IdOP x) y

  refl : {A : Set}(x : A) -> x == x
  refl x = introg (IdOP x) ★

  private
    h' : {A : Set}(x : A)(C : (y : A) -> x == y -> Set1)
         (h : C x (refl x))(a : Gu (IdOP x) (Ug (IdOP x)) (Tg (IdOP x))) ->
         KIH (IdOP x) (Ug (IdOP x)) (Tg (IdOP x)) C a ->
         C (Gi (IdOP x) (Ug (IdOP x)) (Tg (IdOP x)) a) (introg (IdOP x) a)
    h' x C h ★ _ = h

  H : {A : Set}(x : A)(C : (y : A) -> x == y -> Set1)
      (h : C x (refl x))
      (y : A)(p : x == y) -> C y p
  H x C h y p = Rg (IdOP x) C (h' x C h) y p

  H-equality : {A : Set}(x : A)(C : (y : A) -> x == y -> Set1)
               (h : C x (refl x)) ->
               H x C h x (refl x) ≡₁ h
  H-equality x C h = Rg-equality (IdOP x) C (h' x C h) ★

open Christine-Identity
-}
