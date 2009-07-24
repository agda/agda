\documentclass{article}

\begin{document}

  In a literate agda file you can mix \TeX-code (or really arbitrary text) and
  agda code. The agda code appears between {\tt \backslash begin\{code\}} and
  {\tt \backslash end\{code\}}.

\begin{code}

  module Literate where

    aDefinition : Set -> Set
    aDefinition A = A

\end{code}

  You get the best use of this together with the \TeX-compiler (to be
  implemented), which will typeset the agda code super nicely to produce a
  {\em machine-checkable human-readable proof document}.

\begin{code}

    anotherDefinition : Set -> Set -> Set
    anotherDefinition A B = A

\end{code}

  The literate parser works.

\end{document}
