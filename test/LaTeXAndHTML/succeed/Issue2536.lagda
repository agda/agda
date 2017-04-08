\nonstopmode
\documentclass{article}

\usepackage{agda}

\begin{document}

\begin{code}
module _ where
id : {A : Set} → A → A
id x = x
\end{code}

\end{document}
