\section{Cont: The context and operations on it}

All type-checking is done in a context, which consists of an
environment for storing the values and types of all constants. The
context contains only type correct declarations.

The scope analysis guarantees that all constants will have a value and
a type in the context.

This modules contains operations to manipulate the context:
\begin{description}
\item[getVal, getType] looks up the value and type of an identifier.
\item[upCon] updates the context with a new identifier with its value
  and type.
\item[genCon] generates a new constant in the current context.
\item[evalCon] evaluates an expression in a context.
\item[lastCon] looks up the last declaration in the context.
\item[lengthCon] the length of the context.
\end{description}
%if False %% only to be seen by the Haskell compiler
\begin{code}
module Cont where

import Val
import Exp
import Conv
\end{code}
%endif
\begin{code}
type Cont = ([Val],[Val])

getVal   n  (env,tenv)  =  getRef n env
getType  n  (env,tenv)  =  getRef n tenv
-- (getType n cont) looks up the type of the identifier n.

upCon                   :: Val -> Val -> Cont -> Cont
-- upCon u a con adds the declaration i:a=u to the context con
upCon u a (env,tenv)    = (u:env,a:tenv)

genCon                  :: Cont -> Name -> Val -> G Val
genCon (env,_)          = gensym (length env) 
-- genCon con n v generates a new constant with name n and type v. It
-- uses the length of the context     to quarantee that the constant is new.

evalCon                 :: Cont -> Exp -> Val
evalCon (env,_)         = eval env 
-- (evalCon (env, tenv) e) evaluates the expression e in env.

evalBodyCon             :: Cont -> Val -> Exp -> Val
evalBodyCon (env,_)     = evalBody env 

lastCon                 :: Cont -> G (Val,Val,Cont)
lastCon ([],_)          = fail "lastCon"
lastCon (_,[])          = fail "lastCon"
lastCon (u:env,a:tenv)  = return (u,a,(env,tenv))

lengthCon (env,_)       = length env

\end{code}
