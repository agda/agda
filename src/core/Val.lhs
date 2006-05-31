%include lhs2TeX.fmt
\section{Val: Values}
We are using the functions in Haskell to represent the functional
values in the core language.

Constants (i.e. either explicitly defined (abbreviations), implicitly
defined (recursively defined or data types) are represented together
with their concrete name (a string) and their type (which is a
value). A generic value is represented in the same way, except that it
also have an integer which is used to distinguish it from other
generic values.

Domain equation
\begin{displaymath}
  \Val = \lambda\ ( \Val\  \to\  \Val)
 ||\  \App\  H \Val ^*\ ||\  \Set\ 
 ||\  \Fun\  \Val\  (\Val\  \to \Val)
\end{displaymath}
\begin{code}
module Val where

type Name = String

data Val =
     Lam (Val -> Val)
  |  App Head [Val]
  |  Set
  |  Fun Val (Val -> Val)

data Head =
     Gen Int Name Val           -- generic values with a unique tag, name and type
  |  Const Name Val             -- constants with name and type

mvar    :: Head -> Val
-- creates a value (an empty application) from a head.
mvar h  = App h []

mconst      :: Name -> Val -> Val
-- (mconst s v) creates a value from the constant s and the type value v
mconst s v  = mvar (Const s v) 

eqH                              :: Head -> Head -> Bool
-- boolean equality in Head
eqH  (Gen n1 _ _)  (Gen n2 _ _)  = n1 == n2
eqH  (Const s1 _)  (Const s2 _)  = s1 == s2
eqH  _             _             = False

typH               :: Head -> Val
-- (typH h) computes the type of h
typH  (Gen _ _ v)  = v
typH  (Const _ v)  = v

apps                       :: Val -> [Val] -> Val
-- (apps v v1;v2;...;vn) computes (v v1 v2 ... vn)
apps  v            []      = v
apps  (Lam f)      (u:us)  = apps (f u) us
apps  (App h us)   vs      = App h (us ++ vs)

app        :: Val -> Val -> Val
app u1 u2  = apps u1 [u2]

itCurry                  :: Val -> Val -> (Val -> Val) -> Val
itCurry u  (Fun v g)  f  = Fun v (\ w -> itCurry (app u w) (g w) f)
itCurry u  _          f  = f u

inst :: Val -> [Val] -> Val
inst  w          []     = w
inst  (Fun _ f)  (u:us) = inst (f u) us
  
\end{code}

