\section{Conv: Checking convertibility}

%if False %% only to be seen by the Haskell compiler
\begin{code}
module Conv where

import Val
\end{code}
%endif

This module implements convertibility. There are functions which
checks convertibility for values, type values and vector of values.
The convertibility functions take one extra integer argument which is
used for creating
fresh values. This is used when we check if two functional values \texttt{f}
and \texttt{g} are convertible, we just check if \texttt{f u = g u} for a fresh 
value u.

The following functions are defined:
\begin{itemize}
\item  |eq n u v w|   checks if \texttt{v = w : u}
\item |eqs n u vs ws| checks if \texttt{vs = ws : u'}, 
       where \texttt{u'} is the argument types of \texttt{u}
\item |eqT n u v| checks if \texttt{u = v} as types.
\end{itemize}

We first have to define the monad for error checking:
\begin{code}
data G a = Ok a | Fail String

instance  Monad G  where
    (Ok x)   >>= k   =  k x
    Fail s   >>= k   =  Fail s
    return           =  Ok
    fail             =  Fail
\end{code}
The convertibility functions will use a |gensym| function to generate 
fresh generic values. The expression |gensym n s u| will generate an 
empty application from the head built up from the (unique) index |n|, 
the name |s| and the type |u|.
\begin{code}
gensym        :: Int -> Name -> Val -> G Val 
gensym n s u  = return (mvar (Gen n s u))
\end{code}

\subsubsection{Type convertibility}

To check if two types are convertible, we have the following cases:
\begin{itemize}
\item \texttt{Set} is equal to \texttt{Set}.
\item Two functional types are equal if their parts are equal, so to check whether 
\texttt{Fun a f = Fun a' f'} we first check if \texttt{a = a'} and then check if
\texttt{f u = f' u}, where \texttt{u} is a new generic value.
\item For the remaining cases, we check if they are convertible as values in \texttt{Set}
\end{itemize}
\begin{code}
eqT :: Int -> Val -> Val -> G () 

eqT  _  Set          Set          = return ()

eqT  n  (Fun a1 f1)  (Fun a2 f2)  = 
  do
  eqT n a1 a2 
  u <- gensym n "X" a1
  eqT (n+1) (f1 u) (f2 u)

eqT  n  u1           u2           = eq n Set u1 u2
\end{code}

\subsubsection{Convertibility of values in a type}
To check if two objects are equal in a type we have the following cases:
\begin{itemize}
\item If the type is a functional type, then to check \texttt{u = v : Fun a f}, 
we check if \texttt{u w = v w : f w} for a fresh value \texttt{w}.
\item Otherwise, we must check two applications. We then check that the heads are equal
and the arguments are equal.
\end{itemize}
\begin{code}
eq :: Int -> Val -> Val -> Val -> G ()

eq  n       (Fun a f)  u1            u2            =
  do
  u <- gensym n "X" a
  eq (n+1) (f u) (app u1 u) (app u2 u)

eq  n       _          (App h1 us1)  (App h2 us2)  = 
  if eqH h1 h2  then eqs n (typH h1) us1 us2 
                else fail"eq"

eq  _       _          _             _             =  fail "eq"
\end{code}

\subsubsection{Convertibility of vectors}
The expression |eqs n u vs ws| checks if two vectors |vs| and 
|ws| are equal and fits as arguments to the functional type |u|. We have 
the following cases:
\begin{itemize}
\item If the two vectors are empty, then we are done.
\item If the two vectors are nonempty, then to check if 
    \texttt{u1:us1 = u2:us2 : Fun a f} we first check if \texttt{u1 = u2 : a} and 
then check \texttt{us1 = us2 : f u1}.
\end{itemize}

\begin{code}
eqs :: Int -> Val -> [Val] -> [Val] -> G ()   

eqs  n  (Fun a f)  (u1:us1)  (u2:us2) =
  do
  eq n a u1 u2
  eqs n (f u1) us1 us2

eqs  n  a          []        []       = return ()

eqs  _  _          _         _        = fail "eqs" 
\end{code}
