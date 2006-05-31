\section{Check:Type checking expressions for objects and types}
%if False %% only to be seen by the Haskell compiler
\begin{code}
module Check where

import Val
import Conv
import Exp
import Cont
\end{code}
%endif

This module contains functions to check that an expression has a given type, and to check if an expression is a type:
\begin{itemize}
\item 
    |check con v e| will check if |e : v| in the 
      context |con|. We will write this as \texttt{con ::- e : v}.
      Here we assume that the context 
      |con| and the type |v| is already type-checked. 
\item 
    |checkT con e| will check if |e| is a correct type in 
    the context |con|. We will write this as \texttt{con ::- e}

\end{itemize}
\subsubsection{Checking if an expression is a correct type}

In order to check \texttt{con ::- e}, i.e. if the expression \texttt{e}
is a correct type in the context \texttt{con}, we have the following cases:
\begin{itemize}
\item The expression \texttt{e} is \texttt{Set}. Then this is correct.
\item To check if a an expression |Efun a b| is a type, we first check
 that the expression |a| is a type. Then we compute the value |v| of
 |a|. Finally, we check that |b| is a type in the context extended with
 a new generic value x' of type |v|. In summary:
\begin{verbatim}
 con ::- (Fun a b) ;
 v := value of a ;
 con, x':v ::- b
\end{verbatim}
\item In other cases, the expression must be a set, so we check if it
  is an object in \texttt{Set}.
\end{itemize}

\begin{code}
checkT :: Cont -> Exp -> G ()

checkT  con  ESet        =
  return ()

checkT  con  (EFun a b)  =
  do
  checkT con a
  v  <- return (evalCon con a)
  u  <- genCon con "X" v
  checkT (upCon u v con) b

checkT  con  e           = 
  check con Set e
\end{code}
\subsection{Checking if an expression is an object in a type}
When we are checking if an expression has a certain type, then we have
always checked that the type is correct.
In order to check \texttt{con ::- e : v} we look at the shape of |e|:
\begin{itemize}
\item A lambda expression must have a functional type. To check if
  |Elam e| has the type |Fun v f| we check if |e| has the type |f x'|
  in the context extended with |x'|, a new generic value of type |v|.
\item To typecheck an application |EApp n es| we first lookup the type
  of the constant |n|, and then check that the arguments |es| have the
  correct type. In order to do this, we are using a new checking
  function |checkI| which is defined below.
\item If the expression is a body of an implicitly defined constant

... to be filled in later ...

\end{itemize}
\begin{code}
check :: Cont -> Val -> Exp -> G ()  

check  con  (Fun v f)  (ELam e)     =
 do
  u <- genCon con "X" v
  check (upCon u v con) (f u) e

check  con  v          (EApp n es)  = 
-- con ::- n es : v is correct if 
-- the arguments es fits the type of n. We compute the resulting type
-- and check that it is equal to the type of the constant n.
 do 
  v' <- checkI con (getType n con) es
  eqT (lengthCon con) v v'

check  con v          (Efun _ nes)  =
-- con ::- (i1:t1, ..., in:tn) : v is typecorrect if each b
 mapM_ (checkP con v) nes
check _ _ _ = fail "check"
  
\end{code}
\begin{code}
checkP  con  (Fun (App h ps) f)  (_,i,e)  =
-- checks if 

-- ... to be filled in later ...

  do 
  v  <-  return (getVal i con)
  w  <-  return (getType i con)
  check con (itCurry (apps v ps) (inst w ps) f) e

checkP  _    _                   _        = fail "checkP"

-- (checkI con (Fun a f) es) will check if the arguments es will fit the
-- iterated functional type es and return the resulting type.
checkI  _    v          []      = return v
checkI  con  (Fun a f)  (e:es)  =
-- if we the argument list is non-empty we just check recursively
-- if e : a and
-- if es fits (f e') , where e' is the value of e
  do
  check con a e
  checkI con (f (evalCon con e)) es
checkI  _    _          _       = fail "checkI"
 

\end{code}

