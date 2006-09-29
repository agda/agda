\section{Exp: Abstract syntax and evaluation of expressions}

%if False %% only to be seen by the Haskell compiler
\begin{code}
module Exp where
import Val
\end{code}
%endif

We use deBruijn indexes for representing functional expressions. The
abstract syntax of expressions is given by the following:
\begin{code}
data Exp =
       ELam Exp                       -- object expressions
    |  EApp Int [Exp]

    |  ESet                           -- type expressions
    |  EFun Exp Exp

    |  Efun Int [(Name,Int,Exp)]      -- body of an implicit definition
\end{code}
The corresponding concrete syntax is the following:

\begin{tabular}{ll}
  |Elam e|                   & represents \texttt{$\lambda$\ x -> e}\\
  |Eapp i [e1;...]|           &represents \texttt{(i e1 ...)}\\
  |ESet|                     & represents \texttt{Set}\\
  |Efun e1 e2|               &represents \texttt{(x:e1) -> e2}\\
  |Efun i [(n1,j1,e1);...]|   &represents the RHS of a recursive definition\\
                           &\texttt{ = cj x1 x2 x3 -> e  ...} is represented by\\
                           &| Efun m [(cj, j, \x1 x2 x3 -> e) ...]|\\
                           & where \\
                           &    m is the number of hidden arguments\\
                           &    D is the name of the constructor\\
                           &    j is the index of the constructor  \\
\end{tabular}

The evaluator computes the value of an expression in an
environment. The environment is a list of values and is used to store
the values of the variables and defined constants. We will use a
function |update| which updates the environment and a function
|getRef| which looks up the value of a defined constant.
\begin{code}
type Env = [Val]

update        ::  Env -> Val -> Env
update env u  =   u:env
\end{code}
The expression |getRef n env| looksup the value of the n:th constant
    in an environment |env|.
\begin{code}
getRef  0      (u:us)  =  u
getRef  (n+1)  (u:us)  =  getRef n us
getRef  0      []      =  error "getRef"  -- erroneous scope analysis
\end{code}
\begin{code}
eval                     :: Env -> Exp -> Val
eval  env  (ELam e)      =  Lam (\ u -> eval (update env u) e)

eval  env  (EApp n us)   =  apps (getRef n env) (map (eval env) us)

eval  env  ESet          = Set

eval  env  (EFun a1 a2)  =
   Fun (eval env a1) (\ u -> eval (update env u) a2)

eval  env  e             = error "eval"
\end{code}
\begin{code}
get s [] = error ("get " ++ s)     -- should never occur

get s ((s1,u):us) = if s == s1 then u else get s us
\end{code}
\begin{code}
evalBody :: Env -> Val -> Exp -> Val
--  evalBody is used in Decl when typechecking defined constant.
--  evalBody env v e
evalBody env v (ELam e) = Lam (\ u -> evalBody (update env u) (app v u) e)
evalBody env v (Efun k nes) =
 Lam f
  where
        f (App (Const c _) us) = apps (get c nvs) (drop k us)
        f w = app v w
        nvs = map (\ (c,_,e) -> (c,eval env e)) nes
evalBody env v e = eval env e
\end{code}
