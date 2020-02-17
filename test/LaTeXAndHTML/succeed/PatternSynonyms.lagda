\documentclass{article}
\usepackage{agda}
\begin{document}

\begin{code}
data Nat : Set where
  zero : Nat
  suc : Nat → Nat

module PatternSyns where
  pattern two   = suc (suc zero)
  pattern three = suc two

open PatternSyns using (two) renaming (three to three′)

data Bot : Set where
\end{code}

\end{document}
