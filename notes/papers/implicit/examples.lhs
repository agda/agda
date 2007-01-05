
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
%format Sigma = "\Sigma"
%format |-    = "\vdash"
%format omega = "\omega"
%format Omega = "\Omega"
%format C1    = "C_1"
%format C2    = "C_2"
%format zero  = "0"

%format when  = "\mathbf{when}"

%endif

In this section we look at a few examples that illustrates the workings of the
type checker.

\subsubsection{A simple example}

First let us look at a very simple example. Consider the signature |Sigma = Nat : Set,
zero : Nat, id : (A : Set) -> A -> A = \A x. x, alpha : Set| containing a set |Nat| with an
element |zero|, a polymorphic identity function |id|, and a meta-variable
|alpha| of type |Set|. Now we want to compute |M| such that $\CheckTypeCtx {} {|id ?
zero|} {|alpha|} M$. To do this one of the conversion rules have to be applied,
so the type checker first infers the type of |id ? zero|.

{\small\[
    \Rule{ \InferTypeCtx {} {|id ? zero|} {|beta|} {|id beta zero|}}
    {\begin{array}{ccc}
	\begin{array}[b]{lll}
	    \InferTypeCtx {} {|id|} {|(A : Set) -> A -> A|} {|id|}
	&~&  \CheckTypeCtx {} {|?|} {|Set|} {|beta|}
	\end{array}
    &~&	\infer{ \CheckTypeCtx {} {|zero|} {|beta|} {|zero|} }
	{\begin{array}{lll}
	    \InferTypeCtx {} {|zero|} {|Nat|} {|zero|}
	&&  \InstMeta {|beta|} {|Nat|}
	\end{array}}
    \end{array}}
\]}
The inferred type |beta| is then compared against the expected type |alpha|,
resulting in the instantiation $\InstMeta {|alpha|} {|Nat|}$.
The final signature is |Nat : Set|, $0:\mathit{Nat}$, |id : (A : Set) -> A -> A = \A
x. x, alpha : Set = Nat, beta : Set = Nat| and $M = |id beta zero|$. Note that
it is important to look up the values of instantiated meta-variables--it would
not be correct to instantiate |alpha| to |beta|, since |beta| is not in scope
at the point where |alpha| is declared.

\subsubsection{An example with guarded constants}

In the previous example all constraints could be solved immediately so no
guarded constants had to be introduced. Now let us look at an example with
guarded constants. Consider the signature of natural numbers with a case
principle:

\begin{code}
    Nat : Set, zero : Nat, suc : Nat -> Nat,
    caseNat :  (P : Nat -> Set) -> P zero ->
	       ((n : Nat) -> P (suc n)) ->
	       (n : Nat) -> P n
\end{code}

In this signature we want to check that |caseNat ? zero (\n. n)| has type |Nat
-> Nat|. The first thing that happens is that the arguments to |caseNat| are checked
against their expected types. Checking |?| against |Nat -> Set| introduces a
fresh meta-variable
%
\begin{code}
alpha : Nat -> Set
\end{code}
%
Next the inferred type of |zero| is checked against the expected type |alpha
zero|. This produces an unsolved constraint |alpha zero = Nat|, so a guarded
constant is introduced:
%
\begin{code}
p : alpha zero = zero when alpha zero = Nat
\end{code}
%
Similarly, the third argument introduces a guarded constant.
%
\begin{code}
q : (n : Nat) -> alpha (suc n) = \n. n when (n : Nat) |- alpha (suc n) = Nat
\end{code}
%
The resulting type correct approximation is |caseNat alpha p (\n. q n)| of type
|(n : Nat) -> alpha n|.  This type is compared against the expected type |Nat
-> Nat| giving rise to the constraint |alpha n = Nat| which is solvable with
|alpha = \n. Nat|. Once |alpha| is instantiated we can perform a $\Simplify$
step to solve the guards on |p| and |q| and subsequently reduce |caseNat alpha
p (\n. q n)| to |caseNat (\n. Nat) zero (\n. n) : Nat -> Nat|.

\subsubsection{What could go wrong?} \label{secCoerce}

So far we have only looked at type correct examples, where nothing bad would
have happened if we had not introduced guarded constants when we did.  The
following example shows how things can go wrong. Take the signature |Nat : Set,
zero : Nat|. Now add the perfectly well-typed identity function |coerce|:
%
\begin{code}
coerce : (F : Nat -> Set) -> F zero -> F zero = \F x. x
\end{code}
%
For any well-typed term |t : B| and type |A|, |coerce ? t| will successfully
check against |A|, resulting in the constraints |alpha zero = B| and |A = alpha
zero|, none of which can be solved. If we did not introduce guarded constants
|coerce ? t| would reduce to |t| and hence we could use |coerce| to give an
arbitrary type to a term. For instance we can type\footnote{This only type
checks if we allow meta-variables to be instantiated to function types, which
is not the case in {\Core}. However, the type checking algorithm can be
extended to handle this, something we have done in the implementation.}
\begin{code}
omega  : (N -> N) -> N  = \x. x (coerce ? x)
Omega  : N	        = omega (coerce ? omega)
\end{code}
where without guarded constants |Omega| would reduce to the non-normalising
$\lambda$-term |(\x. x x) (\x. x x)|. With our, algorithm new guarded
constants are introduced for for the argument to |coerce| and for the
application of coerce. So the type correct appoximation of |Omega| would be
|omega p| where |p = coerce alpha q when alpha zero = N -> N| and |q = omega
when (N -> N) -> N = alpha zero|.

