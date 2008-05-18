
-- IIRDg is expressible in IIRDr + Identity
module Proof where

open import LF
open import IIRD
open import IIRDr
open import DefinitionalEquality
open import Identity
open import Proof.Setup
import Logic.ChainReasoning as Chain

-- We can then define general IIRDs using the ε function from Proof.Setup.
Ug : {I : Set}{D : I -> Set1} -> OPg I D -> I -> Set
Ug γ = Ur (ε γ)

Tg : {I : Set}{D : I -> Set1}(γ : OPg I D)(i : I) -> Ug γ i -> D i
Tg γ = Tr (ε γ)

introg : {I : Set}{D : I -> Set1}(γ : OPg I D)(a : Gu γ (Ug γ) (Tg γ)) ->
         Ug γ (Gi γ (Ug γ) (Tg γ) a)
introg γ a = intror (G→H γ (Ug γ) (Tg γ) a)

-- To prove the reduction behviour of Tg we first have to prove that the
-- top-level reduction of the encoding behaves as it should. At bit simplified
-- that  Ht (ε γ) (Gi a) ≡ Gt γ a
Tg-eq : {I : Set}{D : I -> Set1}(γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
        (a : Gu γ U T) ->
        Ht (ε γ) U T (Gi γ U T a) (G→H γ U T a) ≡₁ Gt γ U T a
Tg-eq {I}{D} (ι < i | e >') U T ★         = refl-≡₁
Tg-eq        (σ A γ)        U T < a | b > = Tg-eq (γ a) U T b
Tg-eq        (δ A i γ)      U T < g | b > = Tg-eq (γ (T « i × g »)) U T b

-- The statement we're interested in is a special case of the more general
-- lemma above.
Tg-equality : {I : Set}{D : I -> Set1}(γ : OPg I D)(a : Gu γ (Ug γ) (Tg γ)) ->
              Tg γ (Gi γ (Ug γ) (Tg γ) a) (introg γ a) ≡₁ Gt γ (Ug γ) (Tg γ) a
Tg-equality γ a = Tg-eq γ (Ug γ) (Tg γ) a

-- The elimination rule for generalised IIRDs.
-- It's basically the elimination of the encoding followed by the elimination
-- of the proof the the index is the right one.
Rg : {I : Set}{D : I -> Set1}(γ : OPg I D)(F : (i : I) -> Ug γ i -> Set1)
     (h : (a : Gu γ (Ug γ) (Tg γ)) -> KIH γ (Ug γ) (Tg γ) F a -> F (Gi γ (Ug γ) (Tg γ) a) (introg γ a))
     (i : I)(u : Ug γ i) -> F i u
Rg {I}{D} γ F h = Rr (ε γ) F \i a ih ->
                    G→H∘H→G-subst γ U T
                                  (\i a -> F i (intror a))
                                  i a (lem1 i a ih)
  where
    U = Ug γ
    T = Tg γ
    lem1 : (i : I)(a : Hu (ε γ) U T i) ->
           KIH (ε γ i) U T F a ->
           F (Gi γ U T (H→G γ U T i a))
             (intror (G→H γ U T (H→G γ U T i a)))
    lem1 i a ih = h (H→G γ U T i a) (\v -> εIArg-subst γ U T F i a v (ih (εIArg γ U T i a v)))

open module Chain-≡  = Chain.Poly.Heterogenous1 _≡₁_ (\x -> refl-≡₁) trans-≡₁
open module Chain-≡₀ = Chain.Poly.Heterogenous  _≡_  (\x -> refl-≡)  trans-≡
	      renaming (chain>_ to chain>₀_; _===_ to _===₀_; _by_ to _by₀_)

-- Again we have to generalise
Rg-eq : {I : Set}{D : I -> Set1}(γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
        (F : (i : I) -> U i -> Set1)(intro : (a : Gu γ U T) -> U (Gi γ U T a))
        (g : (i : I)(u : U i) -> F i u)
        (h : (a : Gu γ U T) -> KIH γ U T F a -> F (Gi γ U T a) (intro a))
        (a : Gu γ U T) ->
        let i  = Gi γ U T a
            a' = G→H γ U T a
        in h (H→G γ U T i a')
	     (\v -> εIArg-subst γ U T F i a' v
		      (Kmap (ε γ i) U T F g a' (εIArg γ U T i a' v)))
           ≡₁ h a (Kmap γ U T F g a)
Rg-eq {I}{D} γ U T F intro g h a = app-≡₁
  (cong-≡₁⁰ h (H→G∘G→H-identity γ U T a))
  (η-≡₁⁰ \x y p ->
    chain>  εIArg-subst γ U T F i a' x (Kmap (ε γ i) U T F g a' (εIArg γ U T i a' x))
        === Kmap (ε γ i) U T F g a' (εIArg γ U T i a' x)
              by εIArg-identity γ U T F a x (Kmap (ε γ i) U T F g a' (εIArg γ U T i a' x))
        === Kmap γ U T F g a y
              by app-≡₁⁰
                  (cong-≡₁⁰ g
                    (chain>₀ KIArg→I (ε γ i) U T a' (εIArg γ U T i a' x)
                        ===₀ KIArg→I γ U T (H→G γ U T i a') x   by₀  εIArg→I-identity γ U T i a' x
                        ===₀ KIArg→I γ U T a y                  by₀
                                app-≡₀ (cong-≡' (KIArg→I γ U T)
                                                (H→G∘G→H-identity γ U T a)
                                       ) p
                    )
                  )
                  (chain>₀ KIArg→U (ε γ i) U T a' (εIArg γ U T i a' x)
                      ===₀ KIArg→U γ U T (H→G γ U T i a') x   by₀  εIArg→U-identity γ U T i a' x
                      ===₀ KIArg→U γ U T a y                  by₀
                              app-≡₀ (cong-≡' (KIArg→U γ U T)
                                              (H→G∘G→H-identity γ U T a)
                                     ) p
                  )
  )
  where
    i  = Gi γ U T a
    a' = G→H γ U T a

Rg-equality : {I : Set}{D : I -> Set1}(γ : OPg I D)(F : (i : I) -> Ug γ i -> Set1)
              (h : (a : Gu γ (Ug γ) (Tg γ)) -> KIH γ (Ug γ) (Tg γ) F a -> F (Gi γ (Ug γ) (Tg γ) a) (introg γ a))
              (a : Gu γ (Ug γ) (Tg γ)) ->
              Rg γ F h (Gi γ (Ug γ) (Tg γ) a) (introg γ a)
              ≡₁ h a (Kmap γ (Ug γ) (Tg γ) F (Rg γ F h) a)
Rg-equality {I}{D} γ F h a =
  chain> Rg γ F h (Gi γ U T a) (introg γ a)
     === h'' i a' ih    by  refl-≡₁
     === G→H∘H→G-subst γ U T F' i a' (h' i a' ih)
                        by  refl-≡₁
     === h' i a' ih     by G→H∘H→G-identity γ U T F' a (h' i a' ih)
     === h (H→G γ U T i a') (\v -> εIArg-subst γ U T F i a' v (ih (εIArg γ U T i a' v)))
                        by refl-≡₁
     === h a (Kmap γ U T F (Rg γ F h) a)      by  Rg-eq γ U T F (introg γ) (Rg γ F h) h a
  where
    U  = Ug γ
    T  = Tg γ
    F' = \i a -> F i (intror a)
    i  = Gi γ U T a
    a' = G→H γ U T a
    h' : (i : I)(a : Hu (ε γ) U T i) -> KIH (ε γ i) U T F a -> F _ _
    h' = \i a ih -> h (H→G γ U T i a) \v ->
                  εIArg-subst γ U T F i a v
                      (ih (εIArg γ U T i a v))
    h'' = \i a ih -> G→H∘H→G-subst γ U T F' i a (h' i a ih)
    ih  = Kmap (ε γ i) U T F (Rg γ F h) a'

