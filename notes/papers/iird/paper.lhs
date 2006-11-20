\documentclass[11pt]{article}

%include lhs2TeX.fmt
%include lhs2TeX.sty

%if anyMath

%format .   = ".~"
%format Set = "\Set"
%format Type = "\Type"
%format ==  = "=="
%format **  = "×"
%format :   = "\mathrel{:}"

%format zero = "\mathsf{z}"
%format suc  = "\mathsf{s}"
%format refl = "\mathsf{refl}"

%format === = "\equiv"

%format iota	= "ι"
%format sigma	= "σ"
%format delta	= "δ"
%format gamma	= "γ"

%format Even'	= "\mathit{Even}^{*}"
%format evenZ	= "\mathsf{evenZ}"
%format evenSS  = "\mathsf{evenSS}"
%format evenZ'	= "\mathsf{evenZ}^{*}"
%format evenSS' = "\mathsf{evenSS}^{*}"
%format elim_Even = "elim_{Even}"

%format pi0 = "π_0"
%format pi1 = "π_1"

%endif

\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}
\usepackage{color}

\usepackage{amsthm}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{definition}[theorem]{Definition}

% Enables greek letters in math environment
\everymath{\SetUnicodeOption{mathletters}}
\everydisplay{\SetUnicodeOption{mathletters}}

% This makes sure that local glyph overrides below are
% chosen.
\DeclareUnicodeOption{localDefs}
\SetUnicodeOption{localDefs}

% For some reason these macros need to be defined.
\newcommand{\textmu}{$\mu$}
\newcommand{\textnu}{$\nu$}

% This character doesn't seem to be defined by ucs.sty.
\DeclareUnicodeCharacter{"21A6}{\ensuremath{\mapsto}}

\input{macros}

\title{Encoding indexed inductive types using the identity type}
\author{Ulf Norell}

\begin{document}
\maketitle
\begin{abstract}
    An indexed inductive-recursive definition (IIRD) simultaneously defines an
    indexed family of sets and a recursive function over this family.  This
    notion is sufficiently powerful to capture essentially all definitions of
    sets in Martin-Löf type theory.

    I show that it is enough to have one particular indexed inductive type,
    namely the intensional identity relation, to be able to interpret all IIRD
    as non-indexed definitions.
    
    The proof is formally verified in Agda.
\end{abstract}

\section{Introduction}

% Describe the current state of affairs

Indexed induction recursion is the thing.

% Indentify gap

Dybjer and Setzer~\cite{dybjer:indexed-ir} show that in an extensional theory
generalised IIRD can be interpreted by restricted IIRD~\cite{dybjer:jsl}. We're
not using an extensional theory though.

\TODO{What's the relation between restricted IIRD and IRD?}

% Fill gap

I improve on this result showing that it is enough to add intensional equality.
The proof is formalised in Agda.

Non-indexed definitions are simpler(?), so if can get away with just adding the
identity type we get simpler meta theory that if we would add indexed
definitions directly.

\section{The Logical Framework}

    Martin-Löf's logical framework~\cite{nordstrom:book} extended with sigma
    types ($\SIGMA x A B$), $\Zero$, $\One$, and $\Two$.

    \TODO{what about $Π$ in Set? Used on the meta level but probably not on the object level.}

    $\HasType {Γ} x A$

    $\IsType {Γ} A$

    $\PI x A B$

    $\SIGMA x A B$

\section{The Identity Type}

There are many versions.

\begin{code}
    (==)  : {A : Set} -> A -> A -> Set
    refl  : {A : Set}(x : A) -> x == x
\end{code}

Martin-Löf identity relation, introduced in 1973~\cite{martin-lof:predicative}.

\begin{definition}[Martin-Löf elimination]

The Martin-Löf elimination rule (sometimes called $J$) has the type

\begin{code}
elim_ML :  {A : Set}(C : (x, y : A) -> x == y -> Set) ->
	   ((x : A) -> C x x (refl x)) ->
	   (x, y : A)(p : x == y) -> C x y p
\end{code}

and the corresponding computation rule is

> elim_ML C h x x (refl x) = h x

\end{definition}

\begin{definition}[Paulin elimination]
Paulin identity relation~\cite{pfenning-paulin:inductive-coc}.

\begin{code}
elim_P :  {A : Set}(x : A)(C : (y : A) -> x == y -> Set) ->
	  C x (refl x) -> (y : A)(p : x == y) -> C y p
\end{code}

The corresponding computation rule is

> elim_P x C h x (refl x) = h

\end{definition}

\begin{lemma}
    Martin-Löf elimination can be defined in terms of Paulin elimination.
\end{lemma}

\begin{proof}

Trivial.

> elim_ML C h x y p = elim_P x (\z q. C x z q) (h x) y p

\end{proof}

\begin{lemma}
    Paulin elimination can be defined in terms of Martin-Löf elimination.
\end{lemma}

\begin{proof}
    This proof is slightly more involved.

    We first define the substitution rule
\begin{code}
    subst :  {A : Set}(C : A -> Set)(x, y : A)
	     x == y -> C x -> C y
    subst C x y p Cx = elim_ML  (\ a b q. C a -> C b)
			        (\ a Ca. Ca) x y p Cx
\end{code}

    Now define

\begin{code}
    E : {A : Set}(x : A) -> Set
    E x = (y : A) ** (x == y)
\end{code}

    We can prove that any element of |E x| is in fact equal to |(x, refl x)|.

\begin{code}
    uniqE : {A : Set}(x, y : A)(p : x == y) -> (x, refl x) == (y, p)
    uniqE = elim (\ x y p. (x, refl x) == (y, p)) refl
\end{code}

\begin{code}
    elim_P x C h y p = subst  (\ z. C (pi0 z) (pi1 z))
			      (x, refl x) (y, p) (uniqE x y p) h
\end{code}

    Note that in an impredicative setting there is a simpler proof due to
    Streicher~\cite{streicher:habilitation}.

\end{proof}

\begin{theorem}
    Martin-Löf elimination and Paulin elimination are equivalent.
\end{theorem}

Streicher axiom K. Not valid~\cite{HofmannM:gromru}. Fortunately we don't need it.

In the following we will use Paulin elimination.

\section{Indexed Induction Recursion}

Very fancy and general types~\cite{dybjer:indexed-ir}.

\TODO{How much details from \cite{dybjer:indexed-ir}?}

Codes for IIRD.

\begin{code}
    data OP (I : Set)(D : I -> Type)(E : Type) where
	iota   : E -> OP I D E
	sigma  : (A : Set)(gamma : A -> OP I D E) -> OP I D E
	delta  : (A : Set)(i : A -> I)(gamma : ((a : A) -> D (i a))) -> OP I D E
\end{code}

\subsection{Examples}

Intensional identity relation (Paulin version).

\begin{code}
data (==) {A : Set}(x : A) : A -> Set where
    refl : x == x
\end{code}

The elimination rule for this type is Paulin elimination.

\section{Encoding}

Just add a proof that the index is the right one.

Example:

\begin{code}
    data Even : Nat -> Set where
	evenZ   : Even zero
	evenSS  : {n : Nat} -> Even n -> Even (suc (suc n))
\end{code}

    The corresponding elimination rule is:

\begin{code}
    elim_Even :
	(C : (n : Nat) -> Even n -> Set) ->
	C zero evenZ ->
	((n : Nat)(e : Even n) -> C n e -> C (suc (suc n)) (evenSS e)) ->
	(n : Nat)(e : Even n) -> C n e
\end{code}

As a non-indexed type

\begin{code}
    data Even' (n : Nat) : Set where
	evenZ'   : zero == n -> Even' n
	evenSS'  : (m : Nat) -> Even m -> suc (suc m) == n -> Even' n

    evenZ : Even' zero
    evenZ = evenZ' refl

    evenSS : (n : Nat) -> Even n -> Even (suc (suc n))
    evenSS n e = evenSS' n e refl
\end{code}

    To define the elimination rule we eliminate the proof that the index is the
    expected one. 

    The elimination rule in deduction style: We have

> hz   : C z evenZ
> hss  : (n : Nat)(e : Even n) -> C n e -> C (s (s n)) (evenSS n e)
> n    : Nat
> e    : Even n

    and the goal is

> ? : C n e

    By eliminating |e| (using the non-indexed elimination) we get two cases

%format p1 "\mathit{p}_1"
%format p2 "\mathit{p}_2"

> p1  : zero == n
> ?   : C n (evenZ' p1)

    Now we can eliminate |p1|, effectively substituting |z| for |n| and |refl|
    for |p1| in the goal to obtain the new goal

> ? : C zero (evenZ' refl)

    This is exactly the type of |hz|.

    In the second case we get

> ih  : C m e'
> p2  : suc (suc m) == n
> ?   : C n (evenSS' m e' p2)

    Eliminating |p2| yields

> ? : C (suc (suc m)) (evenSS' m e' refl)

    which is the type of

> hss m e' ih

Here is the elimination spelled out. To improve readability I present the
elimination of the interpretation using pattern matching notation and explicit
recursion.

\begin{code}
    elim_Even C hz hss n (evenZ' p)  =
	elim_P zero (\ z q. C zero evenZ') hz n p
    elim_Even C hz hss n (evenSS' m e p)  =
	elim_P  (suc (suc m))
		(\ z q. C (suc (suc m)) (evenSS' e))
		(hss m e (elim_Even C hz hss m e))
		n p
\end{code}

This gives us the correct type for the elimination rule, but we also need the
correct computation rules. Namely

> elim_Even C hz hss zero	    evenZ	  = hz
> elim_Even C hz hss (suc (suc n))  (evenSS n e)  =
>   hss n e (elim_Even C hz hss n e)

The crucial point here is that the equations talk about |evenZ| and |evenSS n
e| and not arbitrary elements of |Even' n|. In these particular cases the proof
object is |refl| so we can use the computation rule of equality elimination to
show the desired computation rules.

\subsection{Formal proof}

The proof is not fully formal. The main issue is that Agda is used both for the
meta level and the object level. This means that it is possible to mix up
object level reasoning and meta level reasoning in an unsound way. I take care
not to do this.

The proof is by (simple) induction over the code for the indexed type.

\section{Related Work}

Peter and Anton obviously~\cite{dybjer:indexed-ir}.

\section{Conclusions}

This is good stuff.

\bibliographystyle{abbrv}
\bibliography{../../../../bib/pmgrefs}

\end{document}
