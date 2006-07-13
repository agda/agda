\section{Decl: Type-checking declarations}
%if False %% only to be seen by the Haskell compiler
\begin{code}
module Decl where

import Val
import Conv
import Exp
import Cont
import Check
\end{code}
%endif

Here we describe how a declaration is type-checked. 

A declaration is either a typing declaration, an explicit definition
or an implicit definition.  There are no data declarations, the scope checker has
translated them to a series of typing
declarations (of the constant denoting the data type and all its
constructors).
\begin{code}
data Decl = Var Name Exp | Def Name Exp | DefRec Name Exp
\end{code}
The type of the
function |checkDeckl| is:
\begin{code}
checkDecl                     :: Decl -> Cont -> G Cont
\end{code}
It takes a declaration and a context
(i.e. the result of type-checked declarations)
and checks the declaration and add it to the context. We have the following cases:
\begin{itemize}
\item \verb|c : E|, a typing of an identifier. We first check that the
  expression \verb|E| is a type, then we compute the value of it and
  update the context with the identifier and its type
\begin{code}
checkDecl  (Var s a)    con   =
  do
  checkT con a
  v <- return (evalCon con a)
  return (upCon v (mconst s v) con)
\end{code}
\item \verb|c = e|, the definition of a constant. We can only define
  the last declared constant. We lookup the type of this and check
  that the right hand side |e| has this type...
\begin{code}
checkDecl  (Def s e)    con   =
  do
  (u,v,con1) <- lastCon con
  check con1 v e
  return (upCon (evalBodyCon con1 (mconst s v) e) v con1)
\end{code}
\item 
\verb|...|, a recursive definition.
\begin{code}
checkDecl  (DefRec s e) con   =
 do
  (_,v,con1) <- lastCon con
  check con v e
  return (mNewCon con1 v s e)
\end{code}
\item 
\end{itemize}
\begin{code}
mNewCon con1 v s e =
  newcon
    where
      w = evalBodyCon newcon (mconst s v) e
      newcon = upCon w v con1

\end{code}




   
