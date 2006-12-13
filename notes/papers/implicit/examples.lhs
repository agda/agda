
%include lhs2TeX.fmt

%if anyMath

%format .     = ".~"
%format alpha = "\alpha"
%format beta  = "\beta"
%format gamma = "\gamma"
%format delta = "\delta"
%format phi   = "\phi"
%format psi   = "\psi"
%format Set   = "\SET"

%endif

In this section we look at a few examples that illustrates the workings of the
type checker.

\subsection{Simple example}

First let us look at a very simple example.

\begin{code}
    id	  : (A : Set) -> A -> A = \A x. x
    Nat   : Set
    zero  : Nat

    z : alpha = id beta zero
\end{code}

In this example we want to compute $M$ such that $\CheckTypeCtx {} {|id beta
zero|} {|alpha|} M$ in the signature $\Sigma = |id : (A : Set) -> A -> A = \A x. x, Nat :
Set, zero : Nat, alpha : Set|$. We assume that we have already checked that
$\IsTypeCtx {} {|alpha|} {|alpha|}$ and hence added |alpha : Set| to the
signature. The type checker will use the conversion rule and so infers the type
of |id beta zero|:

\[
    \infer{ \InferTypeCtx {} {|id beta zero|} {|beta|} {|id beta zero|}}
    {\begin{array}{cc}
	\begin{array}[b]{l}
	    \InferTypeCtx {} {|id|} {|(A : Set) -> A -> A|} {|id|}
	\\  \CheckTypeCtx {} {|beta|} {|Set|} {|beta|}
	\end{array}
    &	\infer{ \CheckTypeCtx {} {|zero|} {|beta|} {|zero|} }
	{\begin{array}{l}
	    \InferTypeCtx {} {|zero|} {|Nat|} {|zero|}
	\\  \InstMeta {|beta|} {|Nat|}
	\end{array}}
    \end{array}}
\]

So the type of |id beta zero| is |beta| and we check
\[
    \infer{ \EqualTypeCtx {} {|alpha|} {|beta|} \emptyset }
    { \InstMeta {|alpha|} {|Nat|} }
\]
The final signature is $|id : (A : Set) -> A -> A = \A x. x, Nat : Set, zero :
Nat, alpha : Set = Nat, beta : Set = Nat|$ and $M = |id beta zero|$. Note that
it is important to look up the values of instantiated meta variables--it would
not be correct to instantiate |alpha| to |beta|, since |beta| is not in scope
at the declaration of |alpha|.

\subsection{An example with guarded constants}

In the previous example all constraints could be solved immediately so no
guarded constants had to be introduced.

\subsection{A dangerous example}

\begin{code}

data N : Set where
  zero : N
  suc  : N -> N

data B : Set where
  true : B
  false : B

F : B -> Set
F true  = N
F false = B

not : B -> B
not true  = false
not false = true

h : ((x : F alpha) -> F (not x)) -> N
h g = g zero

\end{code}

\subsection{A looping example}

\begin{code}
data Fun (A, B : Set) : Set where
  lam : (A -> B) -> Fun A B

app : (A, B : Set) -> Fun A B -> A -> B
app A B (lam f) = f

xx : alpha
xx = lam (\x -> app beta gamma x x)

loop : delta
loop = app phi psi xx xx

\end{code}

