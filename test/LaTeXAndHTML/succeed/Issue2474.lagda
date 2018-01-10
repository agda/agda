\documentclass{article}
\usepackage{agda}
\begin{document}

\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}

postulate
  F : {_ : Set} → Set

A : Set
A = F
\end{code}
\end{document}
