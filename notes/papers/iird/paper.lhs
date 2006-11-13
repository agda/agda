\documentclass[11pt]{article}

%include lhs2TeX.fmt
%include lhs2TeX.sty

%if anyMath

%format .   = ".~"
%format Set = "\Set"
%format ==  = "=="
%format **  = "×"

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
The elimination rule (sometimes called $J$) has the type

\begin{code}
elim_ML :  {A : Set}(C : (x, y : A) -> x == y -> Set) ->
	   ((x : A) -> C x x (refl x)) ->
	   (x, y : A)(p : x == y) -> C x y p
\end{code}

and the corresponding computation rule is

> elim_ML C h x x (refl x) = h x

Paulin identity relation~\cite{pfenning-paulin:inductive-coc}.

\begin{code}
elim_P :  {A : Set}(x : A)(C : (y : A) -> x == y -> Set) ->
	  C x (refl x) -> (y : A)(p : x == y) -> C y p
\end{code}

The corresponding computation rule is

> elim_P x C h x (refl x) = h

\begin{theorem}
    Martin-Löf elimination can be defined in terms of Paulin elimination.
\end{theorem}

\begin{proof}

Trivial.

> elim_ML C h x y p = elim_P x (\z q. C x z q) (h x) y p

\end{proof}

\begin{theorem}
    Paulin elimination can be defined in terms of Martin-Löf elimination.
\end{theorem}

\begin{proof}
    This proof is slightly more involved.

    We first define the substitution rule
\begin{code}
    subst : {A : Set}(C : A -> Set)(x, y : A)
	    x == y -> C x -> C y
    subst C x y p Cx = elim_ML (\ a b q. C a -> C b)
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
    elim_P x C h y p = subst (\ z. C (pi0 z) (pi1 z))
			     (x, refl x) (y, p) (uniqE x y p) h
\end{code}

    Note that in an impredicative setting there is a simpler proof due to
    Streicher~\cite{streicher:habilitation}.

\end{proof}

\begin{corollary}
    Martin-Löf elimination and Paulin elimination are equivalent.
\end{corollary}

Streicher axiom K. Not valid~\cite{HofmannM:gromru}. Fortunately we don't need it.

In the following we will use Paulin elimination.

\section{Indexed Induction Recursion}

Very fancy and general types~\cite{dybjer:indexed-ir}.

\TODO{How much details from \cite{dybjer:indexed-ir}?}

\subsection{Examples}

Intensional identity relation (Paulin version).

\begin{code}
data (==) {A : Set}(x : A) : A -> Set where
    refl : x == x
\end{code}

The elimination rule for this type is Paulin elimination.

\section{Encoding}

Just add a proof that the index is the right one.

\subsection{Proof}

Simple induction over the code for the indexed type.

\section{Related Work}

Peter and Anton obviously~\cite{dybjer:indexed-ir}.

\section{Conclusions}

This is good stuff.

\bibliographystyle{abbrv}
\bibliography{../../../../bib/pmgrefs}

\end{document}
