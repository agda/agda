
module IIRD where

import LF

open LF

data OP (I : Set)(D : I -> Set1)(E : Set1) : Set1 where
  ι : E -> OP I D E
  σ : (A : Set)(γ : A -> OP I D E) -> OP I D E
  δ : (A : Set)(i : A -> I)(γ : ((a : A) -> D (i a)) -> OP I D E) -> OP I D E

_«_×_» : {A, B : Set}{C : B -> Set}{D : B -> Set1}
         (f : (b : B) -> C b -> D b)
         (g : A -> B)(h : (a : A) -> C (g a)) ->
         (a : A) -> D (g a)
f « g × h » = \a -> f (g a) (h a)

Ku : {I : Set}{D : I -> Set1}{E : Set1} -> OP I D E -> (U : I -> Set)(T : (i : I) -> U i -> D i) -> Set
Ku (ι e)     U T = One
Ku (σ A γ)   U T = A × \a -> Ku (γ a) U T
Ku (δ A i γ) U T = ((a : A) -> U (i a)) × \g -> Ku (γ (T « i × g »)) U T

Kt : {I : Set}{D : I -> Set1}{E : Set1}
     (γ : OP I D E)(U : I -> Set)(T : (i : I) -> U i -> D i) ->
     Ku γ U T -> E
Kt (ι e)     U T ★         = e
Kt (σ A γ)   U T < a | b > = Kt (γ a) U T b
Kt (δ A i γ) U T < g | b > = Kt (γ (T « i × g »)) U T b

KIArg : {I : Set}{D : I -> Set1}{E : Set1}
       (γ : OP I D E)(U : I -> Set)(T : (i : I) -> U i -> D i) ->
       Ku γ U T -> Set
KIArg (ι e)     U T ★         = Zero
KIArg (σ A γ)   U T < a | b > = KIArg (γ a) U T b
KIArg (δ A i γ) U T < g | b > = A + KIArg (γ (T « i × g »)) U T b

KIArg→I : {I : Set}{D : I -> Set1}{E : Set1}
          (γ : OP I D E)(U : I -> Set)(T : (i : I) -> U i -> D i) ->
          (a : Ku γ U T) -> KIArg γ U T a -> I
KIArg→I (ι e)     U T ★ ()
KIArg→I (σ A γ)   U T < a | b > c       = KIArg→I (γ a) U T b c
KIArg→I (δ A i γ) U T < g | b > (inl a) = i a
KIArg→I (δ A i γ) U T < g | b > (inr a) = KIArg→I (γ (T « i × g »)) U T b a

KIArg→U : {I : Set}{D : I -> Set1}{E : Set1}
          (γ : OP I D E)(U : I -> Set)(T : (i : I) -> U i -> D i) ->
          (a : Ku γ U T)(v : KIArg γ U T a) -> U (KIArg→I γ U T a v)
KIArg→U (ι e)     U T ★ ()
KIArg→U (σ A γ)   U T < a | b > c       = KIArg→U (γ a) U T b c
KIArg→U (δ A i γ) U T < g | b > (inl a) = g a
KIArg→U (δ A i γ) U T < g | b > (inr a) = KIArg→U (γ (T « i × g »)) U T b a

KIH : {I : Set}{D : I -> Set1}{E : Set1}
      (γ : OP I D E)(U : I -> Set)(T : (i : I) -> U i -> D i) ->
      (F : (i : I) -> U i -> Set1)(a : Ku γ U T) -> Set1
KIH γ U T F a = (v : KIArg γ U T a) -> F (KIArg→I γ U T a v) (KIArg→U γ U T a v)

Kmap : {I : Set}{D : I -> Set1}{E : Set1}
       (γ : OP I D E)(U : I -> Set)(T : (i : I) -> U i -> D i) ->
       (F : (i : I) -> U i -> Set1)
       (g : (i : I)(u : U i) -> F i u)
       (a : Ku γ U T) -> KIH γ U T F a
Kmap γ U T F g a = \v -> g (KIArg→I γ U T a v) (KIArg→U γ U T a v)

-- Things needed for general IIRD

OPg : (I : Set)(D : I -> Set1) -> Set1
OPg I D = OP I D (I ×' D)

Gu : {I : Set}{D : I -> Set1}(γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i) -> Set
Gu γ U T = Ku γ U T

Gi : {I : Set}{D : I -> Set1}(γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
     (a : Gu γ U T) -> I
Gi γ U T a = π₀' (Kt γ U T a)

Gt : {I : Set}{D : I -> Set1}(γ : OPg I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
     (a : Gu γ U T) -> D (Gi γ U T a)
Gt γ U T a = π₁' (Kt γ U T a)

-- Things needed for restricted IIRD

OPr : (I : Set)(D : I -> Set1) -> Set1
OPr I D = (i : I) -> OP I D (D i)

Hu : {I : Set}{D : I -> Set1}
     (γ : OPr I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
     (i : I) -> Set
Hu γ U T i = Ku (γ i) U T

Ht : {I : Set}{D : I -> Set1}
     (γ : OPr I D)(U : I -> Set)(T : (i : I) -> U i -> D i)
     (i : I)(a : Hu γ U T i) -> D i
Ht γ U T i a = Kt (γ i) U T a

-- Some helper functions

infixl 50 _+OP_

_+OP_ : {I : Set}{D : I -> Set1}{E : Set1} -> OP I D E -> OP I D E -> OP I D E
γ₀ +OP γ₁ = σ Two (\x -> case₂ x γ₀ γ₁)

