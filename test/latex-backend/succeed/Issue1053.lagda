\documentclass{article}
\usepackage{agda}
\begin{document}

\begin{code}
id : {A : Set} → A → A
id {A = A} x = x

foo : (A : Set) → A → A
foo B x = id {A = B} x
\end{code}

\end{document}
