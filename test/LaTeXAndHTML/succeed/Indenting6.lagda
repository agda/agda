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
record Equiv (X Y : Set) : Set where
  field
    to    : X → Y
    from  : Y → X
\end{code}

\end{document}
