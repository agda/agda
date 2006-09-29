\section{Cont: The context and operations on it}
%if False %% only to be seen by the Haskell compiler
\begin{code}
module Cont where

import Val
import Exp
import Conv
\end{code}
%endif
All type-checking is done in a context, which consists of an
environment for the values and types of all constants. The
context contains only type correct declarations.
\begin{code}
type Cont = ([Val],[Val])
\end{code}
The scope analysis guarantees that all constants will have a value and
a type in the context.

This modules contains operations to manipulate the context:
\begin{description}
\item[getVal, getType] looks up the value and type of an identifier.
\begin{code}
getVal   n  (env,tenv)  =  getRef n env
getType  n  (env,tenv)  =  getRef n tenv
\end{code}
\item[upCon] updates the context with a new identifier with its value
  and type.
\begin{code}
upCon                   :: Val -> Val -> Cont -> Cont
-- upCon u a con adds the declaration i:a=u to the context con
upCon u a (env,tenv)    = (u:env,a:tenv)
\end{code}
\item[genCon] generates a new constant in the current context. The expression
|genCon con n v| generates a new constant with name |n| and type |v|. It
uses the length of the context to quarantee that the constant is new.
\begin{code}
genCon                  :: Cont -> Name -> Val -> G Val
genCon (env,_)          = gensym (length env) 
\end{code}
\item[evalCon] evaluates an expression in a context. It just strips away the typing
declarations.
\begin{code}
evalCon                 :: Cont -> Exp -> Val
evalCon (env,_)         = eval env 
\end{code}
\item[lastCon] looks up the last declaration in the context.
\begin{code}
lastCon                 :: Cont -> G (Val,Val,Cont)
lastCon ([],_)          = fail "lastCon"
lastCon (_,[])          = fail "lastCon"
lastCon (u:env,a:tenv)  = return (u,a,(env,tenv))
\end{code}
\item[lengthCon] the length of the context.
\begin{code}
lengthCon (env,_)       = length env
\end{code}
\end{description}
\begin{code}
evalBodyCon             :: Cont -> Val -> Exp -> Val
-- evalBodyCon con v e 
evalBodyCon (env,_)     = evalBody env 
-- lastCon con computes the last declaration in con
\end{code}


