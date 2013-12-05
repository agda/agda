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

\end{document}
