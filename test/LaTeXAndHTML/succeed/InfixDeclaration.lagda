\documentclass{article}
\usepackage{agda}

\begin{document}

\begin{code}
module InfixDeclaration where

infix 5 _>>_ _<<_

data _>>_ : Set where
data _<<_ : Set where

\end{code}

Let's try some infix declaration with surrounding text.

\begin{code}
module SurroundingText where

\end{code}

In the following, we declare the fixity of two operators.

\begin{code}
  infix 5 _+_ _*_
\end{code}

A fixity declaration can preceed the actual declaration of the names.

\begin{code}
  postulate _+_ _*_ : Set
\end{code}

Fixity declarations can also occur when renaming during import.

\begin{code}
open SurroundingText renaming (_+_ to infixl 5 _+_;  _*_ to infixl 10 _&_)
\end{code}



\end{document}
