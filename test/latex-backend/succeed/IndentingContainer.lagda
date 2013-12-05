\documentclass{article}

\usepackage{agda}

\begin{document}

\begin{code}
record Sigma (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Sigma public
\end{code}

\begin{code}
uncurry : {A : Set} {B : A → Set} {C : Sigma A B → Set} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Sigma A B) → C p)
uncurry f (x , y) = f x y
\end{code}

\begin{code}
record Container : Set₁ where
  constructor _◃_
  field
    Parameter : Set
    Arity : Parameter → Set
\end{code}

\end{document}
