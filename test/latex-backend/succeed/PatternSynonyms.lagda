\documentclass{article}
\usepackage{agda}
\begin{document}

\begin{code}
data Nat : Set where
  zero : Nat
  suc : Nat → Nat

pattern two   = suc (suc zero)
pattern three = suc two

data Bot : Set where
\end{code}

\end{document}