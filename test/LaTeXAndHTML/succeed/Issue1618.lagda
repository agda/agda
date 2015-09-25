\documentclass{article}
\usepackage{agda}
\setlength{\parindent}{0pt}
\setlength{\parskip}{1ex}
\begin{document}
The let should be properly aligned in the following code:

\begin{code}
id : (A : Set) → A → A
id A =
  let
    id' : B → B
    id' = λ a → a
  in id'
  where
    B : Set
    B = A
\end{code}

This should also work if the new block is following after the
keyword, as opposed to on a new line.

\begin{code}
di : (A : Set) → A → A
di A =
  let  id' : B → B
       id' = λ a → a
  in id'
  where  B : Set
         B = A
\end{code}
\end{document}
