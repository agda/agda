%include agda.fmt

\AgdaHide{
\begin{code}
module Issue854.Terms where

open import Data.Nat
open import Data.List

infixr 3 _to_
\end{code}
}

\subsection{Terms}
\label{terms}

\begin{code}
mutual

  data VTerm : Set where
    var     : (n : ℕ) → VTerm
    con     : (n : ℕ)(p : VTerm) → VTerm
    thunk   : (c : CTerm) → VTerm
    ⟨⟩      : VTerm
    _,_     : (u v : VTerm) → VTerm
    𝟘-elim  : (v : VTerm) → VTerm
    ι₁ ι₂   : (v : VTerm) → VTerm

  data CTerm : Set where
    return force    : (v : VTerm) → CTerm
    _to_            : (c k : CTerm) → CTerm
    let′_be_ split  : (v : VTerm)(k : CTerm) → CTerm
    ⟨⟩              : CTerm
    ƛ_              : (c : CTerm) → CTerm
    _·_             : (f : CTerm)(v : VTerm) → CTerm
    op              : (n : ℕ) → CTerm
    iter            : (φ : List CTerm)(v : VTerm) → CTerm
    run             : (φ : List CTerm)(c : CTerm) → CTerm
    _,_             : (c d : CTerm) → CTerm
    π₁ π₂           : (p : CTerm) → CTerm
\end{code}
