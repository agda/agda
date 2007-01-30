
module Proof.Setup where

import LF
import IIRD
import IIRDr
import DefinitionalEquality
import Identity

open LF
open IIRD
open IIRDr
open DefinitionalEquality
open Identity

-- Given a code for a general IIRD we should give a code for a restricted IIRD.
ε : {I : Set}{D : I -> Set1} -> OPg I D -> OPr I D
ε {I}{D} (ι < j | e >') = \i -> σ (j == i) \p -> ι (subst₁ D p e)
ε        (σ A γ)        = \i -> σ A   \a -> ε (γ a) i
ε        (δ A j γ)      = \i -> δ A j \g -> ε (γ g) i

G→H : {I : Set}{D : I -> Set1}(γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
           (a : Gu γ U T) ->
           Hu (ε γ) U T (Gi γ U T a)
G→H (ι < i | e >') U T ★         = < refl | ★ >
G→H (σ A γ)        U T < a | b > = < a | G→H (γ a) U T b > 
G→H (δ A i γ)      U T < g | b > = < g | G→H (γ (T « i × g »)) U T b >

H→G : {I : Set}{D : I -> Set1}(γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
    (i : I) -> Hu (ε γ) U T i -> Gu γ U T
H→G (ι < j | e >') U T i < p | ★ > = ★
H→G (σ A γ)        U T i < a | b > = < a | H→G (γ a) U T i b >
H→G (δ A j γ)      U T i < g | b > = < g | H→G (γ (T « j × g »)) U T i b >

-- We can turn an inductive argument of the general IIRD to an inductive
-- argument of the restricted version.

H→G∘G→H-identity : {I : Set}{D : I -> Set1}
                   (γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
                   (a : Gu γ U T) ->
                   H→G γ U T (Gi γ U T a) (G→H γ U T a) ≡ a
H→G∘G→H-identity (ι < i | e >') U T ★         = refl-≡
H→G∘G→H-identity (σ A γ)        U T < a | b > = cong-≡ (\z -> < a | z >) (H→G∘G→H-identity (γ a) U T b)
H→G∘G→H-identity (δ A i γ)      U T < g | b > = cong-≡ (\z -> < g | z >)
                                                       (H→G∘G→H-identity (γ (T « i × g »)) U T b)
{-
Gi∘H→G-identity : {I : Set}{D : I -> Set1}
                  (γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
                  (i : I)(b : Hu (ε γ) U T i) ->
                  Gi γ U T (H→G γ U T i b) == i
Gi∘H→G-identity (ι < j | e >') U T i < p | ★ > = p
Gi∘H→G-identity (σ A γ)        U T i < a | b > = Gi∘H→G-identity (γ a) U T i b
Gi∘H→G-identity (δ A j γ)      U T i < g | b > = Gi∘H→G-identity (γ (T « j × g »)) U T i b

Gt∘H→G-identity : {I : Set}{D : I -> Set1}
                  (γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
                  (i : I)(b : Hu (ε γ) U T i) ->
                  Gt γ U T (H→G γ U T i b) ≡₁ Ht (ε γ) U T i b
Gt∘H→G-identity γ U T i b = ?

-- This one ain't true! p ≢ refl : x == y
G→H∘H→G-identity : {I : Set}{D : I -> Set1}
                   (γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
                   (i : I)(b : Hu (ε γ) U T i) ->
                   G→H γ U T (H→G γ U T i b) ≡ b
G→H∘H→G-identity (ι < j | e >') U T i < p | ★ > = ?
G→H∘H→G-identity (σ A γ)        U T i < a | b > = ?
G→H∘H→G-identity (δ A j γ)      U T i < g | b > = ?
-}

-- Rather than proving equalities (which doesn't hold anyway) we provide
-- substitution rules.
G→H∘H→G-subst : {I : Set}{D : I -> Set1}
                (γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
                (F : (i : I)(a : Hu (ε γ) U T i) -> Set1)
                (i : I)(a : Hu (ε γ) U T i)
                (h : F (Gi γ U T (H→G γ U T i a)) (G→H γ U T (H→G γ U T i a))) ->
                F i a
G→H∘H→G-subst (ι < j | e >') U T F i < p | ★ > h = elim==₁ j (\z q -> F z < q | ★ >) h i p
G→H∘H→G-subst (σ A γ)        U T F i < a | b > h =
  G→H∘H→G-subst (γ a) U T (\j c -> F j < a | c >) i b h
G→H∘H→G-subst (δ A j γ)      U T F i < g | b > h =
  G→H∘H→G-subst (γ (T « j × g »)) U T (\j c -> F j < g | c >) i b h

-- Q. When can we remove a G→H∘H→G-subst ?
-- A. When a = G→H γ U T i a'
G→H∘H→G-identity : {I : Set}{D : I -> Set1}
                   (γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
                   (F : (i : I)(a : Hu (ε γ) U T i) -> Set1)
                   (a : Gu γ U T)
                   (h : F (Gi γ U T (H→G γ U T (Gi γ U T a) (G→H γ U T a)))
                          (G→H γ U T (H→G γ U T (Gi γ U T a) (G→H γ U T a)))
                   ) ->
                   G→H∘H→G-subst γ U T F (Gi γ U T a) (G→H γ U T a) h ≡₁ h
G→H∘H→G-identity (ι < i | e >') U T F ★ h = refl-≡₁
G→H∘H→G-identity (σ A γ) U T F < a | b > h =
  G→H∘H→G-identity (γ a) U T (\j  c -> F j < a | c >) b h
G→H∘H→G-identity (δ A i γ) U T F < g | b > h =
  G→H∘H→G-identity (γ (T « i × g »)) U T (\j c -> F j < g | c >) b h

εIArg : {I : Set}{D : I -> Set1}(γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
        (i : I)(a : Hu (ε γ) U T i) ->
        KIArg γ U T (H→G γ U T i a) -> KIArg (ε γ i) U T a
εIArg (ι < j | e >') U T i < h | ★ > ()
εIArg (σ A γ)        U T i < a | b > v       = εIArg (γ a) U T i b v
εIArg (δ A j γ)      U T i < g | b > (inl a) = inl a
εIArg (δ A j γ)      U T i < g | b > (inr v) = inr (εIArg (γ (T « j × g »)) U T i b v)

εIArg→I-identity : {I : Set}{D : I -> Set1}(γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
                   (i : I)(a : Hu (ε γ) U T i)(v : KIArg γ U T (H→G γ U T i a)) ->
                   KIArg→I (ε γ i) U T a (εIArg γ U T i a v)
                   ≡ KIArg→I γ U T (H→G γ U T i a) v
εIArg→I-identity (ι < j | e >') U T i < p | ★ > ()
εIArg→I-identity (σ A γ)        U T i < a | b > v       = εIArg→I-identity (γ a) U T i b v
εIArg→I-identity (δ A j γ)      U T i < g | b > (inl a) = refl-≡
εIArg→I-identity (δ A j γ)      U T i < g | b > (inr v) = εIArg→I-identity (γ (T « j × g »)) U T i b v

εIArg→U-identity : {I : Set}{D : I -> Set1}(γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
                   (i : I)(a : Hu (ε γ) U T i)(v : KIArg γ U T (H→G γ U T i a)) ->
                   KIArg→U (ε γ i) U T a (εIArg γ U T i a v)
                   ≡ KIArg→U γ U T (H→G γ U T i a) v
εIArg→U-identity (ι < j | e >') U T i < p | ★ > ()
εIArg→U-identity (σ A γ)        U T i < a | b > v       = εIArg→U-identity (γ a) U T i b v
εIArg→U-identity (δ A j γ)      U T i < g | b > (inl a) = refl-≡
εIArg→U-identity (δ A j γ)      U T i < g | b > (inr v) = εIArg→U-identity (γ (T « j × g »)) U T i b v


εIArg-subst : {I : Set}{D : I -> Set1}(γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
              (F : (i : I)(u : U i) -> Set1)
              (i : I)(a : Hu (ε γ) U T i)(v : KIArg γ U T (H→G γ U T i a)) ->
              F (KIArg→I (ε γ i) U T a (εIArg γ U T i a v))
                (KIArg→U (ε γ i) U T a (εIArg γ U T i a v)) ->
              F (KIArg→I γ U T (H→G γ U T i a) v)
                (KIArg→U γ U T (H→G γ U T i a) v)
εIArg-subst (ι < j | e >') U T F i < p | ★ > ()      h
εIArg-subst (σ A γ)        U T F i < a | b > v       h = εIArg-subst (γ a) U T F i b v h
εIArg-subst (δ A j γ)      U T F i < g | b > (inl a) h = h
εIArg-subst (δ A j γ)      U T F i < g | b > (inr v) h = εIArg-subst (γ (T « j × g »)) U T F i b v h

εIArg-identity : {I : Set}{D : I -> Set1}
                 (γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
                 (F : (i : I)(u : U i) -> Set1)
                 (a : Gu γ U T)
                 (v : KIArg γ U T (H→G γ U T (Gi γ U T a) (G→H γ U T a)))
                 (h : F (KIArg→I (ε γ (Gi γ U T a)) U T (G→H γ U T a) (εIArg γ U T (Gi γ U T a) (G→H γ U T a) v))
                        (KIArg→U (ε γ (Gi γ U T a)) U T (G→H γ U T a) (εIArg γ U T (Gi γ U T a) (G→H γ U T a) v))
                 ) ->
                 εIArg-subst γ U T F (Gi γ U T a) (G→H γ U T a) v h ≡₁ h
εIArg-identity (ι < i | e >') U T F ★         ()      h
εIArg-identity (σ A γ)        U T F < a | b > v       h = εIArg-identity (γ a) U T F b v h
εIArg-identity (δ A i γ)      U T F < g | b > (inl a) h = refl-≡₁
εIArg-identity (δ A i γ)      U T F < g | b > (inr v) h = εIArg-identity (γ (T « i × g »)) U T F b v h

