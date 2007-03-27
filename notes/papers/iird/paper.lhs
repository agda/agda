\documentclass{llncs}

%include lhs2TeX.fmt
%include lhs2TeX.sty

%if anyMath

%format ~ = "~"

%format ! = "{}"

%format .   = ".~"
%format Set = "\Set"
%format Type = "\Type"
%format ==  = "=="
%format **  = "×"
%format :   = "\mathrel{:}"

\newcommand \zero {\mathsf{z}}
\newcommand \suc  {\mathsf{s}}
%format zero = "\zero"
%format suc  = "\suc"

%format refl = "\mathsf{refl}"

%format === = "\equiv"

%format of_  = "\mathit{of}"

%format iota    = "ι"
%format sigma   = "σ"
%format delta   = "δ"
%format gamma   = "γ"
%format eps     = "ε"
%format beta    = "β"
%format eta     = "η"

%format eps_I   = "ε_I"

%format inl     = "\mathsf{inl}"
%format inr     = "\mathsf{inr}"

%format Even'   = "\mathit{Even}^{*}"
%format evenZ   = "\mathsf{evenZ}"
%format evenSS  = "\mathsf{evenSS}"
%format evenZ'  = "\mathsf{evenZ}^{*}"
%format evenSS' = "\mathsf{evenSS}^{*}"
%format elim_Even = "\mathit{elim}_{\Even}"
%format elim_Even' = "\mathit{elim}_{\Even^{*}}"
\newcommand \Even {\mathit{Even}}

%format pi0 = "π_0"
%format pi1 = "π_1"

%format elim0 = "\mathit{case}_0"
%format elim2 = "\elimBool"
%format Elim2 = "\ElimBool"
\newcommand \elimBool {\mathit{case}_2}
\newcommand \ElimBool {\mathit{case}^{\mathit{type}}_2}

%format OP  = "\mathit{OP}"
%format OPg = "\mathit{OP}^g"
%format OPr = "\mathit{OP}^r"

%format Fin_n       = "\mathit{Fin}_n"
%format Args_IE     = "\mathit{Args}_{I,E}"
%format index_IE    = "\mathit{index}_{I,E}"
%format IndArg_IE   = "\mathit{IndArg}_{I,E}"
%format IndIndex_IE = "\mathit{indIndex}_{I,E}"
%format Ind_IE      = "\mathit{ind}_{I,E}"
%format IndHyp_IE   = "\mathit{IndHyp}_{I,E}"
%format indHyp_IE   = "\mathit{indHyp}_{I,E}"

%format elimUrg     = "\mathit{elim}{-}U^r_γ"
%format elimUreg    = "\mathit{elim}{-}U^r_{εγ}"
%format elimUgg     = "\mathit{elim}{-}U^g_γ"

%format elimId  = "\mathit{elim}_{==}"
%format elim_P  = "\mathit{elim}_{==,PM}"
%format elim_ML = "\mathit{elim}_{==,ML}"
%format elim_K  = "\mathit{elim}_{==,K}"

%format 0 = "\mathbf{0}"
%format 1 = "\mathbf{1}"
%format 2 = "\mathbf{2}"
%format star = "\star"
%format star0 = "\star_0"
%format star1 = "\star_1"

%format < = "\left\langle"
%format > = "\right\rangle"

%format << = "<"
%format =~= = "\cong"

%format Urg     = "U^r_γ"
%format introrg = "\mathrm{intro}^r_γ"

%format Ugg     = "U^g_γ"
%format introgg = "\mathrm{intro}^g_γ"

%format Ureg     = "U^r_{εγ}"
%format introreg = "\mathrm{intro}^r_{εγ}"

%format grArgs = "g{\to}rArgs"
%format grArgs_I = "g{\to}rArgs_I"

%format rgArgs = "r{\to}gArgs"
%format rgArgs_I = "r{\to}gArgs_I"

%format rgArgssubst = "rgArgs{-}subst"

%format ar   = "a_r"
%format arg  = "a_{rg}"
%format stepr = "\mathit{step}_r"

%format IdA   = "\mathrel{{==}_A}"

%endif

\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}
\usepackage{color}

\newcommand \infer[2] {
  \frac
    {\begin{array}{c}\displaystyle #1\end{array}}
    {\begin{array}{c}\displaystyle #2\end{array}}
}

% Enables greek letters in math environment
\everymath{\SetUnicodeOption{mathletters}}
\everydisplay{\SetUnicodeOption{mathletters}}

% This makes sure that local glyph overrides below are
% chosen.
\DeclareUnicodeOption{localDefs}
\SetUnicodeOption{localDefs}

% For some reason these macros need to be defined.
\newcommand \textmu     {$μ$}
\newcommand \textnu     {$ν$}
\newcommand \texteta    {$η$}
\newcommand \textbeta   {$β$}
\newcommand \textlambda {$λ$}

% This character doesn't seem to be defined by ucs.sty.
\DeclareUnicodeCharacter{"21A6}{\ensuremath{\mapsto}}

\input{macros}

\title{Encoding indexed inductive definitions using the intensional identity type}
\author{Ulf Norell}
\institute{Chalmers University of Technology \\
  \email{ulfn@@cs.chalmers.se}
}

\begin{document}
\maketitle
\begin{abstract}
  It is well-known how to represent indexed inductive definitions, or inductive
  families, using extensional equality. We show that this encoding also works
  in intensional type theory and that the computation rules associated with an
  inductive family are preserved. The proof has been formalised in Agda.
\end{abstract}

\section{Introduction}

% Describe the current state of affairs (and sell inductive families)

Indexed inductive definitions (IID), or inductive families, are inductively
defined families of sets. As such they have a wide range of applications in
both mathematics and programming. Examples include the transitive closure of a
relation, the typing relation of simply typed $λ$-calculus, and vectors of a
fixed length.

Indexed inductive definitions have been studied extensively in various
theories, such as Martin-Löf type
theory~\cite{dybjer:sophia,dybjer:bastadfacs}, Calculus of Inductive
Constructions~\cite{paulin:thesis,coquand:bastad}, and Luo's
UTT~\cite{luo:typetheory}, and they are supported by tools building on these
theories. For instance, ALF~\cite{magnussonnordstrom:alf},
Coq~\cite{mohring:inductivedefsincoq}, LEGO~\cite{luo:lego}, and
Epigram~\cite{mcbride:left}. They have even made it into languages such as
Haskell~\cite{pj:gadt}.

% Representing inductive families using equality is well-known

An example of an IID is the predicate |Even| over natural numbers inductively
defined by the rules
\[\begin{array}{ccc}
    \infer{}{\Even \, \zero}
&&  \infer{\Even \, n}{\Even \, (\suc \, (\suc \, n))}
\end{array}\]
We distinguish between generalised IID, such as |Even| above, and restricted
IID where the conclusions must all be of the form $P\,\bar
x$~\cite{dybjer:indexed-ir}.

It is well-known~\cite{feferman94finitary} how to reduce generalised IID to
restricted IID using equality. For instance, the |Even| predicate can be
represented by the restricted IID
\[\begin{array}{ccc}
    \infer{n = \zero}{\Even \, n}
&&  \infer{\Even \, m \quad n = \suc \, (\suc \, m)}{\Even \, n}
\end{array}\]
There are several reasons, both practical and theoretical, why restricted IID
are simpler to work with than generalised IID. A practical advantage is that
the elimination rule for a restricted IID can be presented nicely as pattern
matching~\cite{coquand:patternmatching}. From a theoretical standpoint a
restricted IID has the property that it can be expressed as a fixed-point of an
equation. In the example of |Even|:
\[\Even \, n \Leftrightarrow n = \zero \vee \exists m. \, \Even \, m \wedge n = \suc \, (\suc \, m) \]

From a set theoretic point of view it is clear that the formulation of the
generalised IID as a restricted IID is equivalent to the original formulation,
but in a type theoretic setting it is not so obvious. The reason for this is
that in type theory we are not only interested in provability but also in the
proof terms. In the first formulation of the |Even| predicate we have proof
terms |evenZ| and |evenSS m p|, for a number |m| and a proof |p| that |m| is
even, corresponding to the two rules. We also have a dependent elimination rule
|elim_Even|:
\begin{code}
elim_Even :  (C : (n : Nat) -> Even n -> Set) ->
             C zero evenZ ->
             (  (n : Nat)(e : Even n) -> C n e ->
                C (suc (suc n)) (evenSS n e)) ->
             (n : Nat)(e : Even n) -> C n e
\end{code}
Note that the predicate |C| that we are eliminating over, depends not only on a
natural number, but also on the actual proof term that proves it is even.  The
elimination rule is equipped with two computation rules stating that
> elim_Even C cz css zero           evenZ         = cz
> elim_Even C cz css (suc (suc m))  (evenSS m p)  =
>   css m p (elim_Even C cz css m p)
Now it is not at all clear that the second formulation of |Even| enjoys the
same elimination and computation rules, since the proof terms are quite
different. 

Dybjer and Setzer~\cite{dybjer:indexed-ir} show that in extensional type theory
generalised IID can be reduced to restricted IID, and the main result of the
present paper is to show that this can be done also in intensional type theory.
The difference between extensional and intensional type theory is that in
intensional type theory one distinguishes between provable equality and
definitional equality.  The advantage of this is that proof checking becomes
decidable, but a disadvantage is that the proof checker can only decide
definitional equality, so substituting equals for equals for provable equality
is more cumbersome. The main challenge in relating the two formulations of
indexed inductive definitions in intensional type theory is proving that the
computation rules hold definitionally.

% Fill gap

The main contribution of this paper is a proof that, in intensional type
theory, we can faithfully represent generalised IID in terms of restricted IID
and an intensional equality type.  The proof has been formally verified by the
Agda proof checker~\cite{coquand:stt-lfm99}. The formal proof has been carried
out for the fully general case of indexed inductive-recursive
definitions~\cite{dybjer:indexed-ir}, but for presentation reasons we restrict
ourselves to indexed inductive definitions. Adding a recursive component adds
no difficulties to the proof.

For systems such as Agda, which only support restricted indexed inductive
definitions, our result provides a way to get the power of generalised
inductive families without having to extend the meta-theory.

The rest of this paper is organised as follows. Section~\ref{sec-lf} introduces
the logical framework, Section~\ref{sec-id} gives a brief introduction to the
intensional identity type, Section~\ref{sec-IID} gives a formalisation of
indexed inductive definitions, Section~\ref{sec-Encoding} contains the proof
that generalised IID can be reduced to restricted IID, Section~\ref{sec-formal}
comments on the formal proof, and Section~\ref{sec-concl} concludes.

\section{The logical framework} \label{sec-lf}

We use  Martin-Löf's logical framework~\cite{nordstrom:book} extended with
sigma types |(x : A) ** B|, |0|, |1|, and |2|. This is the same framework as is
used by Dybjer and Setzer and the complete rules can be found
in~\cite{dybjer:indexed-ir}. In contrast to Dybjer and Setzer, however, we work
entirely in intensional type theory.

The type of sets |Set| is closed under dependent sums and products, and if |A :
Set| then |A| is a type.

Dependent function types are written |(x : A) -> B| and have elements |\ x. a|,
where |a : B| provided |x : A|.  Application of |f| to |a| is written |f a|. If
|x| does not occur free in |B| we write |A -> B| for |(x : A) -> B| and when
the result type is itself a function type we write |(x : A)(y : B) -> C| for
|(x : A) -> (y : B) -> C|.

The elements of a sigma type |(x : A) ** B| are pairs |<a, b>| where |a : A|
and $b : B[a/x]$ (|B| with |a| substituted for |x|). We have projections |pi0|
and |pi1| with the |beta|-rules |pi0 <a, b> = a| and |pi1 <a, b> = b| and the
|eta|-rule |<pi0 p, pi1 p> = p|.

The empty type |0| has no elements and elimination rule |elim0 : 0 -> A|, for
any |A : Set|. The element of the singleton type is |star : 1| and if |a : 1|
then |a = star| (|eta|-rule). The two element type |2| has elements |star0| and
|star1|, and elimination rule $\elimBool : (i : \mathbf{2}) \to A[\star_0] \to
A[\star_1] \to A[i]$, where $A[i]$ is a type for |i : 2|. We also have large
elimination for |2|: |Elim2 : 2 -> Set -> Set -> Set|. Using the large
elimination we can define the disjoint union of two types
> A + B = (i : 2) ** Elim2 i A B.

\section{The identity type} \label{sec-id}

In this paper we show that the logical framework extended with restricted IID
and an intensional identity type can express generalised IID. In order to do
this we first have to chose the identity type to use. Let us review our
choices. We want a type
\begin{code}
  ! IdA ! : A -> A -> Set
\end{code}
with introduction rule
\begin{code}
  refl : (x : A) -> x == x
\end{code}

The choice lies in the elimination rule, where we have two principal
candidates. The Martin-Löf elimination rule, introduced in
1973~\cite{martin-lof:predicative} is defined as follows.

\begin{definition}[Martin-Löf elimination]

The Martin-Löf elimination rule (sometimes called $J$) has the type
\begin{code}
elim_ML :  (C : (x, y : A) -> x == y -> Set) ->
           ((x : A) -> C x x (refl x)) ->
           (x, y : A)(p : x == y) -> C x y p
\end{code}
and computation rule
> elim_ML C h x x (refl x) = h x
\end{definition}

A different elimination rule was introduced by
Paulin-Mohring~\cite{pfenning-paulin:inductive-coc}:

\begin{definition}[Paulin-Mohring elimination]
The Paulin-Mohring elimination rule has type
\begin{code}
elim_P :  (x : A)(C : (y : A) -> x == y -> Set) ->
          C x (refl x) -> (y : A)(p : x == y) -> C y p
\end{code}
and computation rule
> elim_P x C h x (refl x) = h

\end{definition}

The difference between Martin-Löf elimination and Paulin-Mohring elimination is
that in Martin-Löf elimination the predicate |C| abstracts over both |x| and
|y|, whereas in Paulin-Mohring elimination the predicate need only abstract
over |y|.

At first glance, Paulin-Mohring elimination looks stronger than Martin-Löf
elimination, and indeed it is easy to define |elim_ML| in terms of |elim_P|.

\begin{lemma}
    Martin-Löf elimination can be defined in terms of Paulin-Mohring
    elimination.
\end{lemma}

\begin{proof}
> elim_ML C h x y p = elim_P x (\ z q. C x z q) (h x) y p
\end{proof}
%
However, it turns out that Paulin-Mohring elimination is also definable in
terms of Martin-Löf elimination~\cite{paulin:mail}. The proof of this is
slightly more involved.
%
\begin{lemma}
    Paulin-Mohring elimination can be defined in terms of Martin-Löf
    elimination.
\end{lemma}

\begin{proof}
    We first define the substitution rule
\begin{code}
    subst :  (C : A -> Set)(x, y : A)
             x == y -> C x -> C y
    subst C x y p Cx = elim_ML  (\ a b q. C a -> C b)
                                (\ a Ca. Ca) x y p Cx
\end{code}
    Now define |E x = (y : A) ** (x == y)|.  We can prove that any element of
    |E x| is equal to |<x, refl x>|.
\begin{code}
    uniqE : (x, y : A)(p : x == y) -> <x, refl x> == <y, p>
    uniqE = elim_ML (\ x y p. <x, refl x> == <y, p>) refl
\end{code}
Finally
\begin{code}
    elim_P x C h y p = subst  (\ z. C (pi0 z) (pi1 z))
                              <x, refl x> <y, p> (uniqE x y p) h
\end{code}
\end{proof}

In an impredicative setting there is a simpler proof due to
Streicher~\cite{streicher:habilitation}. Yet another elimination rule is
Streicher's axiom K~\cite{HofmannM:gromru}, given by
> elim_K :  (x : A)(C : x == x -> Set) ->
>           C refl -> (p : x == x) -> C p
which he shows cannot be defined in terms of the previous elimination rules.

Seeing as Martin-Löf elimination and Paulin-Mohring elimination are equivalent
we choose Paulin-Mohring elimination which is easier to work with. So we extend
our logical framework with
\begin{code}
! IdA !  :  A -> A -> Set
refl     :  (x : A) -> x == x
elimId   :  (x : A)(C : (y : A) -> x == y -> Set) ->
            C x (refl x) -> (y : A)(p : x == y) -> C y p
elimId x C h x (refl x) = h
\end{code}

\section{Indexed Inductive Definitions} \label{sec-IID}

An indexed inductive definition (IID) defines a family of types. We distinguish
between generalised IID, which can be seen as an inductively defined family of
types, and restricted IID, which can be seen as a family of inductive types.
Non-indexed types are a special case of restricted IID, indexed over |1|. For
instance, the type of natural numbers can be seen as the restricted IID
\begin{code}
  Nat   : 1 -> Set
  zero  : (x : 1) -> Nat x
  suc   : (x : 1) -> Nat x -> Nat x
\end{code}
In these cases we omit the index and simply write
\begin{code}
  Nat   : Set
  zero  : Nat
  suc   : Nat -> Nat
\end{code}
An example of a restricted IID indexed by a natural number |n| is the type of
ordered lists of natural numbers greater than or equal to |n|:
\begin{code}
  OrdList  : Nat -> Set
  nil      : (n : Nat) -> OrdList n
  cons     : (n : Nat) -> (m : Nat) -> (m >= n) -> OrdList m -> OrdList n
\end{code}
Note that the introduction rules (constructors) |nil| and |cons|, constructs
elements in |OrdList n| for an arbitrary |n|. Note also that the types at
different indices can depend on each other. In this case the inductive argument
of the |cons| constructor is |OrdList m| for an arbitrary |m >= n|.

In a generalised IID, however, the constructors can target different parts of
the inductive family. In the case of lists of a certain length we have
\begin{code}
  Vec   : Nat -> Set
  nil   : Vec zero
  cons  : (n : Nat) -> Nat -> Vec n -> Vec (suc n)
\end{code}

In the rest of this section we present the formalisation of indexed inductive
types. We follow the formalisation of indexed induction-recursion of Dybjer and
Setzer~\cite{dybjer:indexed-ir} but leave out the recursion to simplify the
presentation.

\subsection{Codes for IID} \label{sec-IID-Codes}

Like Dybjer and Setzer we introduce a common type of codes which will serve
both as codes for general IID and restricted IID.

\begin{code}
OP I E  : Set
iota    : E -> OP I E
sigma   : (A : Set) -> (A -> OP I E) -> OP I E
delta   : (A : Set) -> (A -> I) -> OP I E -> OP I E
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
        booleans given by the formation rule |IsTrue : Bool -> Set| and
        introduction rule |IsTrue true| is |iota true : OPg Bool|
    \item
        Non-inductive argument: |sigma A gamma|. In this case the constructor
        has a non-inductive argument |a : A|. The remaining arguments may depend
        on |a| and are coded by |gamma a|. A datatype with
        multiple constructors can be coded by |sigma C gamma| where |C| is a
        type representing the constructors and |gamma c| is the code for the
        constructor corresponding to |c|. For instance, the code for the
        datatype |Bool| with two nullary constructors is
        \begin{code}
        \i . sigma 2 (\c. elim2 c (iota star) (iota star))
        \end{code}

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

For generalised IID we also need to be able to compute the index of a given
constructor argument.
\begin{code}
index_IE : (gamma : OP I E)(U : I -> Set)(a : Args gamma U) -> E
index (iota e)           U  star    = e
index (sigma A gamma)    U  <x, a>  = index (gamma x) U a
index (delta A i gamma)  U  <_, a>  = index gamma U a
\end{code}
Note that only the non-inductive arguments are used when computing the index.

This is all the machinery needed to introduce the types of generalised and
restricted IID. For restricted IID we introduce, given |gamma : OPr I| and |i :
I|
\begin{code}
    Urg : I -> Set
    introrg i : Args (gamma i) Urg -> Urg i
\end{code}
For generalised IID, given |gamma : OPg I| we want
\begin{code}
    Ugg : I -> Set
    introgg : (a : Args gamma Ugg) -> Ugg (index gamma Ugg a)
\end{code}
In Section~\ref{sec-Encoding} we show how to define |Ugg| in terms of |Urg|.

As an example take the type of pairs over |A| and |B|:
\begin{code}
    gamma = \ i. sigma A (\ a. sigma B (\ b. iota star)) : OPr 1
    Pair A B = Urg : 1 -> Set
    introrg star : A ** (\ a. B ** (\ b. 1)) -> Pair A B star
\end{code}

Note that while the index of a restricted IID is determined from the outside,
it is still possible to have a different index on the inductive occurrences.
An example of this is the accessibility predicate given in
Section~\ref{sec-IID-Codes}. This is crucial when interpreting general IID by
restricted IID (see Section~\ref{sec-Encoding}).

\subsection{Elimination rules} \label{sec-IID-Elimination}

To complete the formalisation of IID we have to give the elimination rules.  We
start by defining the set of assumptions of the inductive occurrences in a
given constructor argument.
\begin{code}
IndArg_IE : (gamma : OP I E)(U : I -> Set) -> Args gamma U -> Set
IndArg (iota e)           U star      = 0
IndArg (sigma A gamma)    U < a, b >  = IndArg (gamma a) U b
IndArg (delta A i gamma)  U < g, b >  = A + IndArg gamma U b
\end{code}
Simply put |IndArg gamma U a| is the disjoint union of the assumptions of the
inductive occurrences in |a|.

Now, given the assumptions of one inductive occurrence we can compute the index
of that occurrence.
\begin{code}
IndIndex_IE :  (gamma : OP I E)(U : I -> Set)
               (a : Args gamma U) -> IndArg gamma U a -> I
indIndex (iota e)           U  star      z        = elim0 z
indIndex (sigma A gamma)    U  < a, b >  c        = indIndex (gamma a) U b c
indIndex (delta A i gamma)  U  < g, b >  (inl a)  = i a
indIndex (delta A i gamma)  U  < g, b >  (inr a)  = indIndex gamma U b a
\end{code}
The code |gamma| contains the values of the indices for the inductive
occurrences so we just have to find the right inductive occurrence.

We can now define a function to extract a particular inductive occurrence from
a constructor argument.
\begin{code}
Ind_IE :  (gamma : OP I E)(U : I -> Set)
          (a : Args gamma U)(v : IndArg gamma U a) -> U (indIndex gamma U a v)
ind (iota e)           U  star      z        = elim0 z
ind (sigma A gamma)    U  < a, b >  c        = ind (gamma a) U b c
ind (delta A i gamma)  U  < g, b >  (inl a)  = g a
ind (delta A i gamma)  U  < g, b >  (inr a)  = ind gamma U b a
\end{code}
Again the definition is very simple.

Next we define the notion of an induction hypothesis. Given a predicate |C|
over elements in a datatype, an induction hypothesis for a constructor argument
|a| is a function that proves the predicate for all inductive occurrences in
|a|.
\begin{code}
IndHyp_IE :  (gamma : OP I E)(U : I -> Set) ->
             (C : (i : I) -> U i -> Set)(a : Args gamma U) -> Set
IndHyp gamma U C a =  (v : IndArg gamma U a) ->
                      C (indIndex gamma U a v) (ind gamma U a v)
\end{code}

Given a function |g| that proves |C i u| for all |i| and |u| we can construct an
induction hypothesis for |a| by applying |g| to all inductive occurrences in
|a|.
\begin{code}
indHyp_IE :
  (gamma : OP I E)(U : I -> Set)
  (C : (i : I) -> U i -> Set)
  (g : (i : I)(u : U i) -> C i u)
  (a : Args gamma U) -> IndHyp gamma U C a
indHyp gamma U C g a = \ v. g (indIndex gamma U a v) (ind gamma U a v)
\end{code}

We are now ready to introduce the elimination rules. Given |I : Set| and |gamma
: OPr I| the elimination rule for the restricted IID |Urg| is given by the
following type and computation rule:
\begin{code}
elimUrg :
  (C : (i : I) -> Urg i -> Set) ->
  ((i : I)(a : Args (γ i) Urg) -> IndHyp (γ i) Urg C a -> C i (introrg i a))
  -> (i : I)(u : Urg i) -> C i u
elimUrg C step i (introrg a) =
  step i a (indHyp (γ i) Urg C (elimUrg C step) a)
\end{code}
That is, for any predicate |C| over |Urg|, if given that |C| holds for all
inductive occurrences in some arbitrary constructor argument |a| then |C| holds
for |introrg a|, then |C| holds for all elements of |Urg|. The computation rule
states that eliminating an element built by the introduction rule is the same
as first eliminating all inductive occurrences and then applying the induction
step.

The elimination rule for a general IID is similar. The difference is that the
index of a constructor argument is computed from the value of the argument.
\begin{code}
elimUgg :
  (C : (i : I) -> Ugg i -> Set) ->
  (  (a : Args γ Ugg) -> IndHyp γ Ugg C a -> C (index γ Ugg a) (introgg a)) ->
  (i : I)(u : Ugg i) -> C i u
elimUgg C step (index γ Ugg a) (introgg a) =
  step a (indHyp γ Ugg C (elimUgg C m) a)
\end{code}

\subsection{Examples} \label{sec-IID-Examples}

%format gammaNat = "γ_{\mathit{Nat}}"
%format introrgn = "\mathit{intro}^r_{γ_{\mathit{Nat}}}"

%format gammaEven = "γ_{\mathit{Even}}"
%format gammaId   = "γ_{{==}}"

As we have seen, datatypes with more than one constructor can be encoded by
having the first argument be a representation of the constructor.  For
instance, the code for natural numbers is
> gammaNat : OPr 1 = \i. sigma 2 (\ c. elim2 c (iota star) (delta 1 (\ x. star) (iota star)))
Here, the first argument is an element of |2| encoding whether the number is
built by |zero| or |suc|. We can recover the familiar introduction rules |zero|
and |suc| by
\begin{code}
zero   = introrgn star ! <star0, star>
suc n  = introrgn star ! <star1, < \ x. n, star> >
\end{code}
Another example is the generalised IID of proofs that a natural numbers are
even given introduction rules
\begin{code}
evenZ  : Even zero
evenSS : (n : Nat) -> Even n -> Even (suc (suc n))
\end{code}
The code for |Even| is
\begin{code}
gammaEven  :  OPg Nat
           =  sigma 2 (\ c. elim2 c (iota zero) (sigma Nat (\ n. delta 1 (\ x. n) (iota (suc (suc n))))))
\end{code}
Again an argument of type |2| is used to distinguish the two constructors. In
the |evenZ| case there are no arguments and the index is |zero|. In the
|evenSS| case there is one non-inductive argument |n| of type |Nat| and one
inductive argument with no assumptions and index |n|. The index of the result
is |suc (suc n)|.

The Paulin-Mohring intensional identity type also has a code. Given a set |A|
and an |x : A| code for the family |x == y| indexed by |y : A| is
\begin{code}
  gammaId : OPg A = iota x
\end{code}
That is, there is a single constructor with no arguments, whose index is |x|.
This corresponds to the introduction rule
> refl : x == x
The elimination rule for this type is exactly the Paulin-Mohring elimination rule.

\section{Encoding generalised IID as restricted IID} \label{sec-Encoding}

In this section we show that generalised IID are expressible in the logical
framework extended with restricted IID and the intensional identity type. We do
this by defining the formation, introduction, and elimination rules of a
generalised IID and subsequently proving that the computation rules hold
intensionally.

\subsection{Formation rule}

We first show how to transform the code for a generalised IID into the code for
its encoding as a restricted IID.  The basic idea, as we have seen, is to add a
proof that the index of the restricted IID is equal to the index computed for
the generalised IID. Concretely:
\begin{code}
eps_I : OPg I -> OPr I
eps (iota i)           j = sigma (i == j) (\ p. iota star)
eps (sigma A gamma)    j = sigma A (\ a. eps (gamma a) j)
eps (delta H i gamma)  j = delta H i (eps gamma j)
\end{code}
Now a generalised IID for a code |gamma| can be defined as the restricted IID
of |eps gamma|.
\begin{code}
Ugg : I -> Set
Ugg i = Ureg i
\end{code}
For example, the generalised IID of the proofs that a number is even, given by
\begin{code}
Even    : Nat -> Set
evenZ   : Even zero
evenSS  : (n : Nat) -> Even n -> Even (suc (suc n))
\end{code}
is encoded by the following restricted IID:
\begin{code}
Even'    : Nat -> Set
evenZ'   : (n : Nat) -> zero == n -> Even' n
evenSS'  : (n : Nat)(m : Nat) -> Even' m -> suc (suc m) == n -> Even' n
\end{code}

\subsection{Introduction rule}

We need an introduction rule
\begin{code}
introgg : (a : Args gamma Ugg) -> Ugg (index gamma Ugg a)
\end{code}
and we have the introduction rule for the restricted IID:
\begin{code}
introreg i  :  Args (eps gamma i) Ureg  -> Ureg i
            =  Args (eps gamma i) Ugg   -> Ugg i
\end{code}
So, what we need is a function |grArgs| to convert a constructor argument for a
generalised IID, |a : Args gamma Ugg|, to a constructor argument for its
representation, |Args (eps gamma (index gamma Ugg a)) Ugg|. This function
simply adds a reflexivity proof to |a|:
\begin{code}
grArgs_I :  (gamma : OPg I)(U : I -> Set)
	    (a : Args gamma U) -> Args (eps gamma (index gamma U a)) U
grArgs (iota e)           U a         = < refl, star >
grArgs (sigma A gamma)    U < a, b >  = < a, grArgs (gamma a) U b >
grArgs (delta H i gamma)  U < g, b >  = < g, grArgs gamma U b >
\end{code}
As usual we abstract over the type of inductive occurrences. Now the
introduction rule is simply defined by
\begin{code}
introgg a = introreg (index gamma Ugg a) (grArgs gamma Ugg a)
\end{code}
In our example:
\begin{code}
evenZ : Even' zero
evenZ = evenZ' refl

evenSS : (n : Nat) -> Even' n -> Even' (suc (suc n))
evenSS n e = evenSS' n e refl
\end{code}

\subsection{Elimination rule}

Now we turn our attention towards the elimination rule.

\begin{theorem}
The elimination rule for a generalised IID is provable for the representation
of generalised IID given above. More precisely, we can prove the following rule
in the logical framework with restricted IID and the identity type.
\begin{code}
elimUgg :  (C : (i : I) -> Ugg i -> Set) ->
           (  (a : Args γ Ugg) -> IndHyp γ Ugg C a ->
              C (index γ Ugg a) (introgg a)) ->
           (i : I)(u : Ugg i) -> C i u
\end{code}
\end{theorem}

\begin{proof}
We can use the elimination for the restricted IID
\begin{code}
elimUreg :  (C : (i : I) -> Ugg i -> Set) ->
            (  (i : I)(a : Args (eps gamma i) Ugg) ->
               IndHyp (eps gamma i) Ugg C a -> C i (introreg i a)) ->
            (i : I)(u : Ugg i) -> C i u
\end{code}
Now we face the opposite problem from what we encountered when defining the
introduction rule. In order to apply the induction step we have to convert a
constructor argument to the restricted IID to a generalised argument, and
likewise for the induction hypothesis. To convert a restricted constructor
argument we simply remove the equality proof.

\begin{code}
rgArgs_I :  (gamma : OPg I)(U : I -> Set)
	    (i : I)(a : Args (eps gamma i) U) -> Args gamma U
rgArgs (iota i)           U j _         = star
rgArgs (sigma A gamma)    U j < a, b >  = < a, rgArgs (gamma a) U j b >
rgArgs (delta H i gamma)  U j < g, b >  = < g, rgArgs gamma U j b >
\end{code}

Converting induction hypotheses requires a little more work. This work,
however, is pure book-keeping, as we will see.  We have an induction hypothesis
for the restricted IID. Namely, for |a : Args (eps gamma i) Ugg| we have
\begin{code}
ih  :  IndHyp (eps gamma i) Ugg C a
    =  (v : IndArg (eps gamma i) U a -> C  (indIndex (eps gamma i) U a v)
                                           (ind (eps gamma i) U a v)
\end{code}
We need, for |a' = rgArgs gamma Ugg i a|
\begin{code}
ih  :  IndHyp gamma Ugg C a'
    =  (v : IndArg gamma U a') -> C (indIndex gamma U a' v) (ind gamma U a' v)
\end{code}
Our intuition is that |eps| does not change the inductive occurrences in any
way, and indeed we can prove the following lemma:

\begin{lemma} \label{lem-eps-ind}
For any closed |gamma|, and |a : Args (eps gamma i) U| and |v : IndArg (eps
gamma i) U a| the following equalities hold definitionally.
\begin{code}
IndArg    gamma U      (rgArgs gamma U i a)    = IndArg    (eps gamma i) U a
indIndex  gamma U      (rgArgs gamma U i a) v  = indIndex  (eps gamma i) U a v
ind       gamma U      (rgArgs gamma U i a) v  = ind       (eps gamma i) U a v
IndHyp    gamma U C    (rgArgs gamma U i a)    = IndHyp    (eps gamma i) U C a
indHyp    gamma U C g  (rgArgs gamma U i a)    = indHyp    (eps gamma i) U C g a
\end{code}
\end{lemma}
%format lem_epsInd = "\ref{lem-eps-ind}"
\begin{proof}
  The first three are proven by induction on |gamma|. The last two follows from the first three.
\end{proof}

That is, we can use the induction hypothesis we have as it is. Let us now try
to define the elimination rule. We are given
\begin{code}
C     :  (i : I) -> Ugg i -> Set
step  :  (a : Args gamma Ugg) -> IndHyp gamma Ugg C a ->
         C (index gamma Ugg a) (introgg a)
i     :  I
u     :  Ugg i
\end{code}
and we have to prove |C i u|. To apply the restricted elimination rule
(|elimUreg|) we need an induction step |stepr| of type
\begin{code}
(i : I)(a : Args (eps gamma i) Ugg) -> IndHyp (eps gamma i) Ugg C a -> C i (intror i a)
\end{code}
As we have observed the induction hypothesis already has the right type, so we attempt to
define
\begin{code}
stepr i a ih = step (rgArgs gamma Ugg i a) ih
\end{code}
The type of |stepr i a ih| is |C (index gamma U ar) (intror (grArgs gamma U
ar))|, where |ar = rgArgs gamma Ugg i a|. Here, we would like the conversion of
a constructor argument from the restricted representation to a generalised
argument and back to be the definitional identity. It is easy to see that
this is not the case.  For instance, in our |Even| example the argument to the
|evenZ'| constructor is a proof |p : zero == zero|. Converting to a generalised
argument we throw away the proof, and converting back we add a proof by
reflexivity. But |p| and |refl| are not definitionally equal. Fortunately they
are provably equal, so we can define the following substitution function:

\begin{code}
rgArgssubst :  (gamma : OPg I)(U : I -> Set)
               (C : (i : I) -> rArgs (eps gamma) U i -> Set)
               (i : I)(a : rArgs (eps gamma) U i) ->
               (C  (index gamma U (rgArgs gamma U i a))
                   (grArgs gamma U (rgArgs gamma U i a))
               ) -> C i a

rgArgssubst (iota i) U C j < p, star > m =
  elimId i (\ k q. C k < q, star >) m j p

rgArgssubst (delta A gamma)   U C j < a, b > m = 
  rgArgssubst (gamma a) U (\ i c. C i < a, c >) j b m

rgArgssubst (delta H i gamma) U C j < g, b > m =
  rgArgssubst gamma U (\ i c. C i < g, c >) j b m
\end{code}
The interesting case is the |iota|-case where we have to prove |C j <p, star>|
given |C i <refl, star>| and |p : i == j|. This is proven using the elimination
rule, |elimId|, for the identity type. Armed with this substitution rule we can
define the elimination rule for a generalised IID:
\begin{code}
elimUgg C step i u = elimUreg C stepr i u
  where
    stepr i a ih = rgArgssubst  gamma Ugg (\ i a. C i (intror i a))
                                i a (step (rgArgs gamma Ugg i a) ih)
\end{code}
\end{proof}

In our example the definition of the elimination rule is
\begin{code}
elim_Even :  (C : (n : Nat) -> Even n -> Set) ->
             C zero evenZ ->
             (  (n : Nat)(e : Even n) -> C n e ->
                C (suc (suc n)) (evenSS n e)) ->
             (n : Nat)(e : Even n) -> C n e
elim_Even C cz css n (evenZ' p)       =
  elimId zero (\ m q. C m (evenZ' q)) cz n p
elim_Even C cz css n (evenSS' m e p)  =
  elimId  (suc (suc m)) (\ z q. C z (evenSS' m e q))
	  (css m e (elim_Even C cz css m e)) n p
\end{code}
To improve readability we present the rule using pattern matching and explicit
recursion rather than calling |elim_Even'|.  The call to |rgArgssubst| is has
been reduced to identity proof eliminations.

\subsection{Computation rule}

So far we have shown that we can represent generalised IID as a restricted IID
and that the elimination rule is still valid. The only thing remaining is to
show that the computation rule is also valid. That is, that we get the same
definitional equalities for our representation as we would if we extended our
system with generalised IID.

\begin{theorem}
  For the representation of generalised IID given above, and the encoding of
  the elimination rule |elimUgg| the following computation rule holds
  definitionally for closed |gamma|:
\begin{code}
elimUgg C step (index γ Ugg a) (introgg a) =
  step a (indHyp γ Ugg C (elimUgg C step) a)
\end{code}
\end{theorem}

\begin{proof}
The key insight here is that the computation rule does not talk about arbitrary
elements of |Ugg|, but only those that have been constructed using the
introduction rule. This means that we do not have to satisfy any definitional
equalities for elements where the equality proof is not definitionally equal to
|refl|. So, the main step in the proof is to prove that |rgArgssubst| is the
definitional identity when the equality proof is |refl|, i.e. when the argument
is build using the |grArgs| function.

\begin{lemma} \label{lem-rgArgsubst}
  For all closed |gamma|, and all |U|, |C|, |a : Args gamma U|, and
  \begin{code}
    h : C (index gamma U arg) (grArgs gamma U arg)
  \end{code}
  where
  \begin{code}
    ar    = grArgs gamma U a
    i     = index gamma U a
    arg   = rgArgs gamma U i ar
  \end{code}
  it holds definitionally that
  \begin{code}
    rgArgssubst gamma U C i ar h = h
  \end{code}
\end{lemma}

%format lem_rgArgsubst = "\ref{lem-rgArgsubst}"

\begin{proof}
  By induction on |gamma|. In the |iota|-case we have to prove that
  \begin{code}
    elimId i C' h i refl = h
  \end{code}
  which is exactly the computation rule for the identity type.
\end{proof}

The final lemma we need before proving the computation rule is that starting with
a generalised constructor argument, converting it to a restricted one, and then
back is the definitional identity. This amounts to adding a reflexivity proof
and then removing it, so it is easy to see that this should be true.

\begin{lemma} \label{lem-arg-is-a}
  For all closed |gamma|, and all |a : Args gamma U| it holds definitionally that
> rgArgs gamma U (index gamma U a) (grArgs gamma U a) = a
\end{lemma}
%format lem_argIsa = "\ref{lem-arg-is-a}"
\begin{proof}
  By induction on |gamma|.
\end{proof}

Now we are ready to prove the computation rule. Take |a : Args gamma Ugg| and let
\begin{code}
  i   = index gamma Ugg a
  ar  = grArgs gamma Ugg a
  arg = rgArgs gamma Ugg i ar
\end{code}
we have
\begin{code}
elimUgg C step (index gamma Ugg a) (introgg a)
=  elimUgg C step i (introgg a)
=  {definition of_ elimUgg and introrg}
   elimUreg C stepr i (introreg i ar)
=  {computation rule for Ureg}
   stepr i ar (indHyp (eps gamma i) Ugg C (elimUgg C step) ar)
=  {definition of_ stepr}
   rgArgssubst gamma Ugg (\ i a. C i (intror i ar)) i ar
      (step arg (indHyp (eps gamma i) Ugg C (elimUgg C step) ar))
=  {Lemma lem_rgArgsubst}
   step arg (indHyp (eps gamma i) Ugg C (elimUgg C step) ar)
=  {Lemma lem_epsInd}
   step arg (indHyp gamma Ugg C (elimUgg C step) arg)
=  {Lemma lem_argIsa}
   step a (indHyp gamma Ugg C (elimUgg C step) a)
\end{code}
\end{proof}

In the example of |Even| the proofs of the computation rules are
\begin{code}
elim_Even C cz css zero evenZ
= elim_Even C cz css zero (evenZ' refl)
= elimId zero (\ m q. C m (evenZ' q)) cz zero refl
= cz

elim_Even C cz css (suc (suc m)) (evenSS m p)
= elim_Even C cz css (suc (suc m)) (evenSS' m p refl)
= elimId  (suc (suc m)) (\ z q. C z (evenSS' m e q))
          (css m e (elim_Even C cz css m e)) (suc (suc m)) refl
= css m e (elim_Even C cz css m e)
\end{code}
The important steps are the appeals to the computation rule for the identity
type.

This concludes the proof that we can faithfully represent generalised IID in
the theory of restricted IID and the intensional identity type.

\section{Notes on the formal proof} \label{sec-formal}

One approach to formalise our result would be to do a deep embedding,
formalising the logical framework and the theory of restricted IID in Agda, and
prove our theorems for this formalisation. This would be a big undertaking,
however, so we chose a more light-weight approach. In Agda we can define the
rules for restricted IID directly, that is, we can define restricted IID as a
datatype in Agda and get the introduction, elimination, and computation rules
for free. Using this definition of restricted IID we can then prove the
formation, introduction, and elimination rules for the representation of
generalised IID.

When we want to prove the computation rule, however, there is a problem. The
computation rule talks about definitional equality and in Agda we cannot reason
about the internal definitional equality. To solve this problem we axiomatised
the definitional equality of the logical framework. That is, for each |A, B :
Set| we introduce a constant
\begin{code}
  ! = ! : A -> B -> Set
\end{code}
and axioms corresponding to the conversion rules of the logical framework. For
instance, for all |f|, |g|, |x|, and |y|
\begin{code}
  app : (f = g) -> (x = y) -> (f x = g y)
\end{code}
In this axiom, we can see why the definitional equality has type |A -> B ->
Set|: since |f| and |g| can be dependent functions, |f x| and |g y| can have
different types.

With this approach one has to be careful with induction.  For instance, if one
proves by induction on |n| that |n + zero = n|, this only holds definitionally
for closed |n|.  In our case the only induction is over codes |gamma| and we
always assume |gamma| to be closed. The formalisation can be downloaded from
the author's webpage~\cite{norell:iird-formal}.

\section{Conclusions} \label{sec-concl}

We have shown that the theory of generalised indexed inductive definitions can
be interpreted in the theory of restricted indexed inductive definitions
extended with an intensional identity type. The informal proof presented here
has been formalised in Agda using a light-weight approach where Agda is used
both for the object language and the meta language.

This result gives way of adding generalised IID to theories with only
restricted IID, such as Agda, without having to extend the meta-theory.

\bibliographystyle{abbrv}
\bibliography{../../../../bib/pmgrefs,iird}

\end{document}

% vim: et
