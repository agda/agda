\section{Val: Values}
%if False %% only to be seen by the Haskell compiler
\begin{code}
module Val where
\end{code}
\%endif

We are using the functions in Haskell to represent the functional
values in the core language.

Constants (i.e. either explicitly defined (abbreviations), implicitly
defined (recursively defined or data types) are represented together
with their concrete name (a string) and their type (which is a
value). A generic value is represented in the same way, except that it
also have an integer which is used to distinguish it from other
generic values.

The set of values is defined by the following domain equation:
\begin{displaymath}
  \Val = \lambda\ ( \Val\  \to\  \Val)
 ||\  \App\  \Hh\  \Val ^*\ ||\  \Set\ 
 ||\  \Fun\  \Val\  (\Val\  \to \Val)
\end{displaymath}
This can be expressed in Haskell by the following data type:
\begin{code}
data Val =
     Lam (Val -> Val)
  |  App Head [Val]
  |  Set
  |  Fun Val (Val -> Val)
\end{code}
The head of a function application is either a constant or a generic
     variable. In both cases it is represented as a name together with
     its type. A generic variable comes together with an integer to distinguish it
     from other generic variables. We use the function |typH| to
     compute the type of a head. 
\begin{code}
data Head =
     Gen Int Name Val           -- generic variables
  |  Const Name Val             -- constants
eqH                              :: Head -> Head -> Bool
-- boolean equality in Head
eqH  (Gen n1 _ _)  (Gen n2 _ _)  = n1 == n2
eqH  (Const s1 _)  (Const s2 _)  = s1 == s2
eqH  _             _             = False

type Name = String

typH               :: Head -> Val
-- (typH h) computes the type of h
typH  (Gen _ _ v)  = v
typH  (Const _ v)  = v
\end{code}
We need functions to convert a constant and a type to a head applied
   to no arguments:
\begin{code}
mvar    :: Head -> Val
-- creates a value (an empty application) from a head.
mvar h  = App h []

mconst      :: Name -> Val -> Val
-- (mconst s v) creates a value from the constant s and the type value v
mconst s v  = mvar (Const s v) 
\end{code}
The expression |apps v [v1; ...; vn]| computes the application
 |v v1 ... vn|
\begin{code}
apps                       :: Val -> [Val] -> Val
-- (apps v v1;v2;...;vn) computes (v v1 v2 ... vn)
apps  v            []      = v
apps  (Lam f)      (u:us)  = apps (f u) us
apps  (App h us)   vs      = App h (us ++ vs)

app        :: Val -> Val -> Val
app u1 u2  = apps u1 [u2]
\end{code}
The expression |itCurry|

 to be completed

\begin{code}

itCurry                  :: Val -> Val -> (Val -> Val) -> Val
itCurry u  (Fun v g)  f  = Fun v (\ w -> itCurry (app u w) (g w) f)
itCurry u  _          f  = f u

inst :: Val -> [Val] -> Val
inst  w          []     = w
inst  (Fun _ f)  (u:us) = inst (f u) us
  
\end{code}

