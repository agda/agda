
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
%format |-    = "\vdash"

%format when  = "\mathbf{when}"

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

In this example we want to compute $M$ such that $\CheckTypeCtx {} {|id ?
zero|} {|alpha|} M$ in the signature $\Sigma = |id : (A : Set) -> A -> A = \A
x. x, Nat : Set, zero : Nat, alpha : Set|$. We assume that we have already
checked that $\IsTypeCtx {} {|alpha|} {|alpha|}$ and hence added |alpha : Set|
to the signature. The type checker will use the conversion rule and so infers
the type of |id ? zero|:

\[
    \infer{ \InferTypeCtx {} {|id ? zero|} {|beta|} {|id beta zero|}}
    {\begin{array}{cc}
	\begin{array}[b]{l}
	    \InferTypeCtx {} {|id|} {|(A : Set) -> A -> A|} {|id|}
	\\  \CheckTypeCtx {} {|?|} {|Set|} {|beta|}
	\end{array}
    &	\infer{ \CheckTypeCtx {} {|zero|} {|beta|} {|zero|} }
	{\begin{array}{l}
	    \InferTypeCtx {} {|zero|} {|Nat|} {|zero|}
	\\  \InstMeta {|beta|} {|Nat|}
	\end{array}}
    \end{array}}
\]

So the type of |id ? zero| is |beta| and we check
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
fresh meta variable
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
|alpha = \n. Nat|. This solution also solves the guards of the guarded
constants, so we can reduce |caseNat alpha p (\n. q n)| to |caseNat (\n. Nat)
zero (\n. n) : Nat -> Nat|.

\subsection{What could go wrong?} \label{secCoerce}

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
zero|, none of which can be solved. If we didn't introduce guarded constants
|coerce ? t| would reduce to |t| and hence we could use |coerce| to give an
arbitrary type to a term.

