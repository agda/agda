\documentclass{article}

\usepackage[references]{agda}

\begin{document}

\begin{code}
module Tag where

module Apa where

bepa : Set → Set
bepa x = x

data Cepa : Set where
  cepa : Cepa

record Depa : Set₁ where
  field
    depa : Set

postulate
  epa : Set

postulate
  α   : Set
  _∘_ : Set
\end{code}

\begin{tabular}{ll}
  Name & Test \\
  \hline
  Apa   & \AgdaRef{Apa} \\
  bepa  & \AgdaRef{bepa} \\
  Cepa  & \AgdaRef{Cepa} \\
  cepa  & \AgdaRef{cepa} \\
  Depa  & \AgdaRef{Depa} \\
  depa  & \AgdaRef{depa} \\
  epa   & \AgdaRef{epa} \\
  α     & \AgdaRef{α} \\
  \_∘\_ & \AgdaRef{\_∘\_} \\
\end{tabular}

\end{document}
