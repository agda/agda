\documentclass{article}

\usepackage{agda}

\begin{document}

\AgdaHide
\begin{code}
module LaTeX where
\end{code}
}

\begin{code}
data Bool : Set where
  true   : Bool
  false  : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true   then t else f = t
if false  then t else f = f

data ℕ : Set where
  zero  : ℕ
  suc   : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero             + n = n
suc m {- ugh -}  + n = suc (m + n)

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

alignment : (m n o p : ℕ) → ℕ
alignment  0  1     2  3     =  4
alignment     1  2  3  4  =  5
alignment        2  3  4  5     = 6
alignment           _  _  _  _  = 0
\end{code}

\begin{code}
data ⊥ : Set where

record R : Set₁ where
  field
    f  : Set
    g  : Set

record R′ (A B : Set) : Set₁ where
  field
    h  : Set
    j  : Set
    r  : R
\end{code}

\begin{code}
module M where
  r′ : ∀ {A B : Set} → R′ A B
  r′ = record
    { h  = ⊥
    ; j  = ⊥
    ; r = record
        { f  = ⊥
        ; g  = ⊥
        }
    }
\end{code}

\end{document}