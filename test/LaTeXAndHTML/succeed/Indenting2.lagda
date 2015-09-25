\documentclass{article}

\usepackage{agda}

\begin{document}

\begin{code}
data Nat : Set where
  zero  : Nat
  suc   : Nat -> Nat
\end{code}

\end{document}
