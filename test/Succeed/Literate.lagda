
In literate Agda everything that is not inside a code block
is considered a comment.

\begin{code}
module Literate where
\end{code}

We can define the natural numbers as follows. First the type

\begin{code}
data Nat : Set where
\end{code}

and then the constructors

\begin{code}
  zero : Nat
  suc  : Nat -> Nat
\end{code}

