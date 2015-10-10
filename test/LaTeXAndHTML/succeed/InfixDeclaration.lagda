\documentclass{article}
\usepackage{agda}
\setmainfont[Ligatures=TeX]{XITS}
\setmathfont{XITS Math}

\begin{document}

\begin{code}
module InfixDeclaration where

infix 5 _>>_ _<<_

data _>>_ : Set where
data _<<_ : Set where

\end{code}
\end{document}
