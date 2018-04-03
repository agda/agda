\documentclass{article}

\usepackage{agda}

\begin{document}

\AgdaHide{
\begin{code}
module LaTeX-succeed where
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

Andreas, 2018-04-03: The following two modules test the highlighting of projection patterns.

\begin{code}
module QualifiedProjectionPatterns where

  r : R
  r .R.f = Bool
  r .R.g = ⊥

  r′ : R′ Bool ⊥
  R′.h r′ = ⊥
  R′.j r′ = Bool → Bool
  R′.r r′ = r
\end{code}

\begin{code}
module UnqualifiedProjectionPatterns where
  open R; open R′

  r₀ : R
  r₀ .f = Bool
  r₀ .g = ⊥

  r′ : R′ Bool ⊥
  h r′ = ⊥
  j r′ = Bool → Bool
  r r′ = r₀
\end{code}

\end{document}
