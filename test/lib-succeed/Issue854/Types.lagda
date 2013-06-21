%include agda.fmt

\subsection{Types}
\label{types}

\AgdaHide{
\begin{code}
module Issue854.Types where

open import Data.Product
open import Data.List

open import Issue854.Context

infixr 3 _⇒_
infixr 4 _⊗_
infixr 4 _&_
infixr 5 _⋆_
\end{code}
}

\begin{code}
mutual

  -- Value types.
  data VType : Set where

    -- Thunk
    ⁅_⁆  : (C : CType) → VType

    -- Products
    𝟙    : VType
    _⊗_  : (U V : VType) → VType

    -- Sums
    𝟘    : VType
    _⊕_  : (U V : VType) → VType

    μ    : (Δ : Sig) → VType

  -- Computation types.
  data CType : Set where

    -- Returns
    _⋆_  : (Σ : Sig)(V : VType) → CType

    -- Function space
    _⇒_  : (V : VType)(C : CType) → CType

    -- Products
    ⊤′   : CType
    _&_  : (B C : CType) → CType

  Op  = VType × VType
  Sig = List Op
\end{code}

\begin{code}
Ctx = Snoc VType

OpAlg : Op → CType → CType
OpAlg (P , A) C = P ⇒ ⁅ A ⇒ C ⁆ ⇒ C

Alg : Sig → CType → List CType
Alg []       C = []
Alg (ω ∷ Ω)  C = OpAlg ω C ∷ Alg Ω C

OpPHomo : Op → Sig → VType → VType → Sig → VType → CType
OpPHomo (P , A) Σ U I Σ′ V =
    P ⇒ ⁅ A ⇒ ((Σ ++ Σ′) ⋆ U & (I ⇒ Σ′ ⋆ V)) ⁆ ⇒ I ⇒ Σ′ ⋆ V

PHomo′ : Sig → Sig → VType → VType → Sig → VType → List CType
PHomo′ []       Σ U I Σ′ V = (U ⇒ I ⇒ Σ′ ⋆ V) ∷ []
PHomo′ (ω ∷ Ω)  Σ U I Σ′ V = OpPHomo ω Σ U I Σ′ V ∷ PHomo′ Ω Σ U I Σ′ V

PHomo : Sig → VType → VType → Sig → VType → List CType
PHomo Σ U I Σ′ V = PHomo′ Σ Σ U I Σ′ V
\end{code}
