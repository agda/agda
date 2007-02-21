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

%format OP  = "\mathit{OP}"
%format OPg = "\mathit{OP}^g"
%format OPr = "\mathit{OP}^r"

%format Fin_n    = "\mathit{Fin}_n"
%format Args_IE  = "\mathit{Args}_{I,E}"
%format index_IE = "\mathit{index}_{I,E}"

%format 1 = "\mathbf{1}"
%format star = "\star"

%format < = "\left\langle"
%format > = "\right\rangle"

%format << = "<"

%format Urg     = "U^r_γ"
%format introrg = "\mathrm{intro}^r_γ"

%format Ugg     = "U^g_γ"
%format introgg = "\mathrm{intro}^g_γ"

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

\section{Indexed Inductive Datatypes} \label{sec-IID}

In this section we present the formalisation of indexed inductive types. We
follow the formalisation of indexed induction recursion of Dybjer and
Setzer~\cite{dybjer:indexed-ir} but leave out the recursion to simplify the
presentation.

\subsection{Codes for IID} \label{sec-IID-Codes}

In accordance with Dybjer and Setzer we introduce a common type of codes which
will serve both as codes for general IID and restricted IID.

\begin{code}
data OP (I : Set)(E : Set) where
  iota   : E -> OP I E
  sigma  : (A : Set)(gamma : A -> OP I E) -> OP I E
  delta  : (A : Set)(i : A -> I)(gamma : OP I E) -> OP I E
\end{code}

Now the codes for general indexed inductive types are defined by |OPg I = OP I
I|, and the codes for restricted types are |OPr I = I -> OP I 1|. The intuition
is that for general IID the index is computed from the shape of the value,
whereas the index of a restricted IID is given beforehand. With these
definitions in mind, let us study the type of codes in more detail. We have
three constructors:
\begin{itemize}
    \item
        Base case: |iota e|. This corresponds to an IID with no arguments to the
        constructor. In the case of a general IID we have to give the index for
        the constructor. For instance the code for the singleton type of true
        booleans given by |IsTrue : Bool -> Set| and introduction rule |IsTrue
        true| is
        \begin{code}
            iota true : OPg Bool
        \end{code}
    \item
        Non-inductive argument: |sigma A gamma|. In this case the constructor
        has a non-inductive argument |a : A|. The remaining arguments may depend
        on |a| and are coded by |gamma a|. For instance, a datatype with
        |n| constructors can be coded by |sigma Fin_n gamma|, where |Fin_n| is
        an |n| element type and |gamma i| is the code for the |i|th constructor.

        Another example is the type of pairs over |A| and |B|
        \begin{code}
            \ i. sigma A (\ a. sigma B (\ b. iota star)) : OPr 1
        \end{code}
        In this case the following arguments do not depend on the value of the
        non-inductive arguments.
    \item
        Inductive argument: |delta A i gamma|. For an inductive argument we
        need to know the index of the argument. Note that the following
        arguments cannot depend on the value of the inductive argument. The
        inductive argument may occur under some assumptions |A|. For example
        consider the accessible part of a relation |<<| over |A|, |Acc : A ->
        Set| with introduction rule that for any |x|, if |((y : A) -> y << x
        -> Acc y)| then |Acc x|. Here the inductive argument |Acc y| occurs
        under the assumptions |(y : A)| and |y << x|. The code for this type is
        \begin{code}
            \ x. delta ((y : A) ** (y << x)) pi0 (iota star) : OPr A
        \end{code}
        The index of the inductive argument is |y| which is the first projection
        of the assumptions.
\end{itemize}
See Section~\ref{sec-IID-Examples} for more examples.

\subsection{From codes to types} \label{sec-IID-Types}

Now that we have defined the codes for IID the next step is to describe their
semantics, i.e. what the elements of an IID with a given code are. First we
define the type of arguments to the constructor parameterised by the type of
inductive arguments\footnote{Analogous to when you for simple inductive types
define an inductive type as the fixed point of some functor.}.
\begin{code}
Args_IE : (gamma : OP I E)(U : I -> Set) -> Set
Args (iota e)           U  = 1
Args (sigma A gamma)    U  = A ** \ a. Args (gamma a) U
Args (delta A i gamma)  U  = ((a : A) -> U (i a)) ** \ d. Args gamma U
\end{code}
There are no surprises here, in the base case there are no arguments, in the
non-inductive case there is one argument |a : A| followed by the rest of the
arguments (which may depend on |a|). In the inductive case we have a function
from the assumptions |A| to a value of the inductive type at the specified
index.

For general IID we also need to be able to compute the index of a given
constructor argument.
\begin{code}
index_IE : (gamma : OP I E)(U : I -> Set)(a : Args gamma U) -> E
index (iota e)           U  _	    = e
index (sigma A gamma)    U  <x, a>  = index (gamma x) U a
index (delta A i gamma)  U  <_, a>  = index gamma U a
\end{code}
Note that only the non-inductive arguments are used when computing the index.

This is all the machinery needed to define the types of general and restricted
IID. For restricted IID we have, given |gamma : OPr I| and |i : I|
\begin{code}
    Urg : I -> Set
    introrg i : Args (gamma i) Urg -> Urg i
\end{code}
For general IID, given |gamma : OPg I| we have
\begin{code}
    Ugg : I -> Set
    introgg : (a : Args gamma Ugg) -> Ugg (index gamma Ugg a)
\end{code}

As an example take the type of pairs over |A| and |B|:

\begin{code}
    gamma = \ i. sigma A (\ a. sigma B (\ b. iota star)) : OPr 1
    Pair A B = Urg : 1 -> Set
    introrg star : A ** (\ a. B ** (\ b. 1)) -> Pair A B star
\end{code}

Note that while the index of a restricted IID is determined from the outside we
still allow so called nested types~\cite{bird98nested}. An example of this is
the accessibility predicate given in Section~\ref{sec-IID-Codes}. This is
crucial when interpreting general IID by restricted IID (see
Section~\ref{sec-Encoding}).

\subsection{Elimination rules} \label{sec-IID-Elimination}

\subsection{Examples} \label{sec-IID-Examples}

Intensional identity relation (Paulin version).

\begin{code}
data (==) {A : Set}(x : A) : A -> Set where
    refl : x == x
\end{code}

The elimination rule for this type is Paulin elimination.

\section{Encoding} \label{sec-Encoding}

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

\begin{code}
elim_Even C hz hss zero	    evenZ	        = hz
elim_Even C hz hss (suc (suc n))  (evenSS n e)  =
   hss n e (elim_Even C hz hss n e)
\end{code}

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
