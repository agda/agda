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

%format bot     = "\bot"

%format Even'   = "\mathit{Even}^{*}"
%format evenZ   = "\mathsf{evenZ}"
%format evenSS  = "\mathsf{evenSS}"
%format evenZ'  = "\mathsf{evenZ}^{*}"
%format evenSS' = "\mathsf{evenSS}^{*}"
%format elim_Even = "elim_{\Even}"
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
%format IndIndex_IE = "\mathit{IndIndex}_{I,E}"
%format Ind_IE      = "\mathit{Ind}_{I,E}"
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

\title{Encoding indexed inductive types using the identity type}
\author{Ulf Norell}
\institute{Chalmers University of Technology \\
  \email{ulfn@@cs.chalmers.se}
}

\begin{document}
\maketitle
\begin{abstract}
  Indexed inductive definitions.

  It is well-known how to represent inductive families using equality. This is
  usually done in an extensional setting. We show that this encoding also works
  in intensional type theory and that the definitional equalities are preserved.

  The proof is formally verified in Agda.
\end{abstract}

\section{Introduction}

% Describe the current state of affairs (and sell inductive families)

Indexed inductive definitions, or inductive families, are inductively defined
families of sets. As such they have a wide range of applications in both
mathemathics and programming. Examples include the transitive closure of a
relation, the typing relation of simply typed λ-calculus, and vectors of a
fixed length.

Indexed inductive definitions have been studied extensively in various
theories, such as Martin-Löf type
theory~\cite{dybjer:sophia,dybjer:bastadfacs}, Calculus of Inductive
Constructions~\cite{paulin:thesis,coquand:bastad}, and Luo's
UTT~\cite{luo:typetheory}, and they are supported by tools building on these
theories. For instance, ALF~\cite{magnussonnordstrom:alf},
Coq~\cite{mohring:inductivedefsincoq}, and Epigram~\cite{mcbride:left}. They
have even made it into more mainstream languages such as Haskell~\cite{pj:gadt}.

\TODO{ Lawvere $[?]$, LEGO $[?]$ }

% Representing inductive families using equality is well-known

It is well-known~\cite{feferman94finitary} how to represent inductively defined
relations using equality. For instance, the predicate |Even| over natural
numbers, inductively defined by
\[\begin{array}{ccc}
    \infer{}{\Even \, \zero}
&&  \infer{\Even \, n}{\Even \, (\suc \, (\suc \, n))}
\end{array}\]
can be characterised by the following formula:
\[
    \Even \, n \Leftrightarrow
      n = \zero \vee
      \exists m. \, \Even \, m \wedge n = \suc \, (\suc \, m)
\]
From a set theoretic point of view it is clear that the two formulations are
equivalent, but in a type theoretic setting it is not so obvious. The reason
for this is that in type theory we are not only interested in provability but
also in the proof terms. In the first formulation of the |Even| predicate we
have proof terms |evenZ| and |evenSS m p|, for a number |m| and a proof |p|
that |m| is even, corresponding to the two rules. We also have a dependent
elimination rule |elim_Even| for proofs of |Even n| which states that for any
predicate |C| over a natural number {\it and a proof that it is even}, if |hz|
is a proof of |C zero evenZ| and |hss| is a function that given |m : Nat|, |q :
Even n| and a proof of |C m q| returns a proof of |C (suc (suc m)) (evenSS m
q)|, then |elim_Even C hz hss n p| proves |C n p| for any natural number |n|
and proof |p| of |Even n|.  This elimination rule is equipped with two
computation rules stating that
> elim_Even C hz hss zero           evenZ         = hz
> elim_Even C hz hss (suc (suc m))  (evenSS m p)  =
>   hss m p (elim_Even C hz hss m p)
Now it is not at all clear that the second formulation of |Even| enjoys the
same elimination and computation rules, since the proof terms are quite
different. 

Dybjer and Setzer~\cite{dybjer:indexed-ir} show that in extensional type theory
the two formulations are equivalent, but to the author's knowledge it has not
been made explicit what the relationship is in intensional type theory. The
difference between extensional and intensional type theory is that in
intensional type theory one distinguishes between provable equality and
definitional equality.  The advantage of this is that proof checking becomes
decidable, but a disadvantage is that the proof checker can only decide
definitional equality, so substituting equals for equals for provable equality
is more cumbersome. The main challenge in relating the two formulations of
indexed inductive definitions in intensional type theory is proving that the
computation rules hold definitionally.

% Fill gap

The main contribution of this paper is a proof that, in intensional type
theory, we can faithfully represent general indexed inductive definitions in
terms of {\em restricted} indexed inductive definitions (families of inductive
definitions rather than inductive families) and an intensional equality type.
The proof has been formally verified by the Agda proof
checker~\cite{coquand:stt-lfm99}, using the intensional type theory of Agda for
the meta reasoning as well as for the object language. The formal proof has
been carried out for the fully general case of indexed inductive-recursive
definitions~\cite{dybjer:indexed-ir}, but for presentation reasons we restrict
ourselves to indexed inductive definitions. Adding a recursive component adds
nothing interesting to the proof.

% Say something about why this is useful.

The rest of this paper is organised as follows. Section~\ref{sec-lf} introduces
the logical framework, Section~\ref{sec-id} gives a brief introduction to the
intensional equality type, Section~\ref{sec-IID} gives a formalisation of
indexed inductive definitions, Section~\ref{sec-Encoding} contains the proof
that a generalised IID can be expressed using a restricted IID, and
Section~\ref{sec-concl} concludes.

\section{The logical framework} \label{sec-lf}

We use  Martin-Löf's logical framework~\cite{nordstrom:book} extended with
sigma types |(x : A) ** B|, |0|, |1|, and |2|. This is the same framework as is
used by Dybjer and Setzer and the complete rules can be found
in~\cite{dybjer:indexed-ir}. In contrast to Dybjer and Setzer we work entirely
in intensional type theory.

The type of sets |Set| is closed under pi and sigma, and if |A : Set| then |A|
is a type.

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
A[\star_1] \to A[i]$, where $A[i]$ is a type when |i : 2|. We also have large
elimination for |2|: |Elim2 : 2 -> Set -> Set -> Set|. Using the large
elimination we can define the disjoint union of two types |A + B = (i : 2) **
Elim2 i A B|.

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

The choice lies in the elimination rule. The Martin-Löf elimination rule,
introduced in 1973~\cite{martin-lof:predicative} is defined as follows.

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
Paulin-Mohring~\cite{pfenning-paulin:inductive-coc}.

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
However, it turns out that Paulin-Mohring elimination is definable in terms of
Martin-Löf elimination. The proof of this is slightly more involved.
%
\begin{lemma}
    Paulin-Mohring elimination can be defined in terms of Martin-Löf
    elimination.
\end{lemma}

\begin{proof}
    We first define the substitution rule
\begin{code}
~
    subst :  (C : A -> Set)(x, y : A)
             x == y -> C x -> C y
    subst C x y p Cx = elim_ML  (\ a b q. C a -> C b)
                                (\ a Ca. Ca) x y p Cx
~
\end{code}
    Now define |E x = (y : A) ** (x == y)|.  We can prove that any element of
    |E x| is equal to |<x, refl x>|.
\begin{code}
~
    uniqE : (x, y : A)(p : x == y) -> <x, refl x> == <y, p>
    uniqE = elim_ML (\ x y p. (x, refl x) == (y, p)) refl
~
\end{code}
Finally
\begin{code}
~
    elim_P x C h y p = subst  (\ z. C (pi0 z) (pi1 z))
                              <x, refl x> <y, p> (uniqE x y p) h
~
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

\section{Indexed Inductive Datatypes} \label{sec-IID}

In this section we present the formalisation of indexed inductive types. We
follow the formalisation of indexed induction recursion of Dybjer and
Setzer~\cite{dybjer:indexed-ir} but leave out the recursion to simplify the
presentation.

\subsection{Codes for IID} \label{sec-IID-Codes}

In accordance with Dybjer and Setzer we introduce a common type of codes which
will serve both as codes for general IID and restricted IID.

\begin{code}
~
data OP (I : Set)(E : Set) where
  iota   : E -> OP I E
  sigma  : (A : Set)(gamma : A -> OP I E) -> OP I E
  delta  : (A : Set)(i : A -> I)(gamma : OP I E) -> OP I E
~
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
        ~
            iota true : OPg Bool
        ~
        \end{code}
    \item
        Non-inductive argument: |sigma A gamma|. In this case the constructor
        has a non-inductive argument |a : A|. The remaining arguments may depend
        on |a| and are coded by |gamma a|. For instance, a datatype with
        |n| constructors can be coded by |sigma Fin_n gamma|, where |Fin_n| is
        an |n| element type and |gamma i| is the code for the |i|th constructor.

        Another example is the type of pairs over |A| and |B|
        \begin{code}
        ~
            \ i. sigma A (\ a. sigma B (\ b. iota star)) : OPr 1
        ~
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
        ~
            \ x. delta ((y : A) ** (y << x)) pi0 (iota star) : OPr A
        ~
        \end{code}
        The index of the inductive argument is |y| which is the first projection
        of the assumptions.
\end{itemize}
See Section~\ref{sec-IID-Examples} for more examples.

\TODO{Explain what we are allowed to do with codes (on the meta level). Take
care to distinguish meta level and object level.}

\subsection{From codes to types} \label{sec-IID-Types}

Now that we have defined the codes for IID the next step is to describe their
semantics, i.e. what the elements of an IID with a given code are. First we
define the type of arguments to the constructor parameterised by the type of
inductive arguments\footnote{Analogous to when you for simple inductive types
define an inductive type as the fixed point of some functor.}.
\begin{code}
~
Args_IE : (gamma : OP I E)(U : I -> Set) -> Set
Args (iota e)           U  = 1
Args (sigma A gamma)    U  = A ** \ a. Args (gamma a) U
Args (delta A i gamma)  U  = ((a : A) -> U (i a)) ** \ d. Args gamma U
~
\end{code}
There are no surprises here, in the base case there are no arguments, in the
non-inductive case there is one argument |a : A| followed by the rest of the
arguments (which may depend on |a|). In the inductive case we have a function
from the assumptions |A| to a value of the inductive type at the specified
index.

For general IID we also need to be able to compute the index of a given
constructor argument.
\begin{code}
~
index_IE : (gamma : OP I E)(U : I -> Set)(a : Args gamma U) -> E
index (iota e)           U  _       = e
index (sigma A gamma)    U  <x, a>  = index (gamma x) U a
index (delta A i gamma)  U  <_, a>  = index gamma U a
~
\end{code}
Note that only the non-inductive arguments are used when computing the index.

This is all the machinery needed to introduce the types of general and restricted
IID. For restricted IID we introduce, given |gamma : OPr I| and |i : I|
\begin{code}
~
    Urg : I -> Set
    introrg i : Args (gamma i) Urg -> Urg i
~
\end{code}
For general IID, given |gamma : OPg I| we want
\begin{code}
~
    Ugg : I -> Set
    introgg : (a : Args gamma Ugg) -> Ugg (index gamma Ugg a)
~
\end{code}
In Section~\ref{sec-Encoding} we show that it is sufficient to introduce
restricted IID together with an intensional identity type, to be able to define
|Ugg|.

As an example take the type of pairs over |A| and |B|:
\begin{code}
~
    gamma = \ i. sigma A (\ a. sigma B (\ b. iota star)) : OPr 1
    Pair A B = Urg : 1 -> Set
    introrg star : A ** (\ a. B ** (\ b. 1)) -> Pair A B star
~
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
~
IndArg_IE : (gamma : OP I E)(U : I -> Set) -> Args gamma U -> Set
IndArg (iota e)           U _         = 0
IndArg (sigma A gamma)    U < a, b >  = IndArg (gamma a) U b
IndArg (delta A i gamma)  U < g, b >  = A + IndArg gamma U b
~
\end{code}
Simply put |IndArg gamma a| is the disjoint union of the assumptions of the
inductive occurrences in |a|.

Now, given the assumptions of one inductive occurrence we can compute the index
of that occurrence.
\begin{code}
~
IndIndex_IE :  (gamma : OP I E)(U : I -> Set)
               (a : Args gamma U) -> IndArg gamma U a -> I
IndIndex (iota e)           U  _         bot
IndIndex (sigma A gamma)    U  < a, b >  c        = IndIndex (gamma a) U b c
IndIndex (delta A i gamma)  U  < g, b >  (inl a)  = i a
IndIndex (delta A i gamma)  U  < g, b >  (inr a)  = IndIndex gamma U b a
~
\end{code}
The code |gamma| contains the values of the indices for the inductive
occurrences so we just have to find the right inductive occurrence.

We can now define a function to extract a particular inductive occurrence from
a constructor argument.
\begin{code}
~
Ind_IE :  (gamma : OP I E)(U : I -> Set)
          (a : Args gamma U)(v : IndArg gamma U a) -> U (IndIndex gamma U a v)
Ind (iota e)           U  _         bot
Ind (sigma A gamma)    U  < a, b >  c        = Ind (gamma a) U b c
Ind (delta A i gamma)  U  < g, b >  (inl a)  = g a
Ind (delta A i gamma)  U  < g, b >  (inr a)  = Ind gamma U b a
~
\end{code}
Again the definition is very simple.

Next we define the notion of an induction hypothesis. Given a predicate |C|
over elements in a datatype, an induction hypothesis for a constructor argument
|a| is a function that proves the predicate for all inductive occurrences in
|a|.
\begin{code}
~
IndHyp_IE :  (gamma : OP I E)(U : I -> Set) ->
             (C : (i : I) -> U i -> Set)(a : Args gamma U) -> Set
IndHyp gamma U C a =  (v : IndArg gamma U a) ->
                      C (IndIndex gamma U a v) (Ind gamma U a v)
~
\end{code}

Given a function |g| that proves |C i u| for all |i| and |u| we can construct an
induction hypothesis for |a| by applying |g| to all inductive occurrences in
|a|.
\begin{code}
~
indHyp_IE :
  (gamma : OP I E)(U : I -> Set)
  (C : (i : I) -> U i -> Set)
  (g : (i : I)(u : U i) -> C i u)
  (a : Args gamma U) -> IndHyp gamma U C a
indHyp gamma U C g a = \ v -> g (IndIndex gamma U a v) (Ind gamma U a v)
~
\end{code}

We are now ready to introduce the elimination rules. Given |I : Set| and |gamma
: OPr I| the elimination rule for the restricted IID |Urg| is given by the
following type and computation rule:
\begin{code}
~
elimUrg :
  (C : (i : I) -> Urg i -> Set) ->
  (  (i : I)(a : Args (γ i) Urg) ->
     IndHyp (γ i) Urg C a -> C i (introrg i a)) ->
  (i : I)(u : Urg i) -> C i u
elimUrg C step i (introrg a) =
  step i a (indHyp (γ i) Urg C (elimUrg C step) a)
~
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
~
elimUgg :
  (C : (i : I) -> Ugg i -> Set) ->
  (  (a : Args γ Ugg) -> IndHyp γ Ugg C a ->
     C (index γ Ugg a) (introgg a)) ->
  (i : I)(u : Ugg i) -> C i u
elimUgg C step (index γ Ugg a) (introgg a) =
  step a (indHyp γ Ugg C (elimUgg C m) a)
~
\end{code}

\TODO{examples}

\subsection{Examples} \label{sec-IID-Examples}

Datatypes with multiple constructors.

Intensional identity relation (Paulin version).

\begin{code}
~
data (==) {A : Set}(x : A) : A -> Set where
  refl : x == x
~
\end{code}

The elimination rule for this type is Paulin elimination.

\section{Encoding generalised IID as restricted IID} \label{sec-Encoding}

\subsection{Formation rule}

To show that generalised IID are expressible in the system of restricted IID
extended with the intensional identity type, we first show how to transform the
code for a generalised IID into the code for its encoding as a restricted IID.
The basic idea is to add a proof that the index of the restricted IID is equal
to index computed for the generalised IID. Concretely:

\begin{code}
~
eps_I : OPg I -> OPr I
eps (iota i)           j = sigma (i == j) (\ _ -> iota star)
eps (sigma A gamma)    j = sigma A (\ a -> eps (gamma a) j)
eps (delta H i gamma)  j = delta H i (eps gamma j)
~
\end{code}

For example, the generalised IID of proof that a number is even, given by
\begin{code}
~
data Even : Nat -> Set where
  evenZ   : Even zero
  evenSS  : (n : Nat) -> Even n -> Even (suc (suc n))
~
\end{code}
is encoded by the following restricted IID:
\begin{code}
~
data Even' (n : Nat) : Set where
  evenZ'   : zero == n -> Even' n
  evenSS'  : (m : Nat) -> Even m -> suc (suc m) == n -> Even' n
~
\end{code}

Using the coding function |eps| we represent the general IID for a code |gamma
: OPg I| as
\begin{code}
~
Ugg : I -> Set
Ugg i = Ureg i
~
\end{code}
In the case that the equality proofs added by |eps| are extensional there is an
equivalence between the generalised IID and its representation as a restricted
IID as shown by Dybjer and Setzer~\cite{dybjer:indexed-ir}. With an intensional
equality proof, however, this is not the case. For instance, for |p, q : zero
== n| it is not necessarily the case that |evenZ' p = evenZ' q|. This means
that our representation of generalised IID contains more elements than the ones
corresponding to elements in the generalised IID. The crucial insight of this
paper is that this does not matter. As long as the extra elements are
well-behaved, i.e. as long as the elimination rule is valid there is no
problem. Before tackling the elimination rule, however, we look at the
introduction rule.

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
~
grArgs_I :  (gamma : OPg I)(U : I -> Set)
	    (a : Args gamma U) -> Args (eps gamma (index gamma U a)) U
grArgs (iota e)           U a         = < refl, star >
grArgs (sigma A gamma)    U < a, b >  = < a, grArgs (gamma a) U b >
grArgs (delta H i gamma)  U < g, b >  = < g, grArgs gamma U b >
~
\end{code}
As usual we abstract over the type of inductive occurrences. Now the
introduction rule is simply defined by
\begin{code}
~
introgg a = introreg (index gamma Ugg a) (grArgs gamma Ugg a)
~
\end{code}
In our example:
\begin{code}
~
evenZ : Even' zero
evenZ = evenZ' refl

evenSS : (n : Nat) -> Even' n -> Even' (suc (suc n))
evenSS n e = evenSS' n e refl
~
\end{code}

\subsection{Elimination rule}

As we have already observed, the representation of a generalised IID contains
more elements than necessary, so it not obvious that we will be able to define
the elimination rule we want. Fortunately it turns out that we can. First,
recall the elimination rule that we want to define:
\begin{code}
~
elimUgg :  (C : (i : I) -> Ugg i -> Set) ->
           (  (a : Args γ Ugg) -> IndHyp γ Ugg C a ->
              C (index γ Ugg a) (introgg a)) ->
           (i : I)(u : Ugg i) -> C i u
~
\end{code}
The elimination for the restricted IID is
\begin{code}
~
elimUreg :  (C : (i : I) -> Ugg i -> Set) ->
            (  (i : I)(a : Args (eps gamma i) Ugg) ->
               IndHyp (eps gamma i) Ugg C a -> C i (introreg i a)) ->
            (i : I)(u : Ugg i) -> C i u
~
\end{code}
Now we face the opposite problem from what we encountered when defining the
introduction rule. In order to apply the induction step we have to convert a
constructor argument to the restricted IID to a generalised argument, and
likewise for the induction hypothesis. To convert a restricted constructor
argument we simply remove the equality proof.

\begin{code}
~
rgArgs_I : (gamma : OPg I)(U : I -> Set)
	   (i : I)(a : Args (eps gamma i) U) -> Args gamma U
rgArgs (iota i)           U j _         = star
rgArgs (sigma A gamma)    U j < a, b >  = < a, rgArgs (gamma a) U j b >
rgArgs (delta H i gamma)  U j < g, b >  = < g, rgArgs gamma U j b >
~
\end{code}

Converting induction hypotheses requires a little more work. This work,
however, is pure book-keeping, as we will see.  We have an induction hypothesis
for the restricted IID. Namely, for |a : Args (eps gamma i) Ugg| we have
\begin{code}
ih  :  IndHyp (eps gamma i) Ugg C a
    =  (v : IndArg (eps gamma i) U a -> C  (IndIndex (eps gamma i) U a v)
                                           (Ind (eps gamma i) U a v)
\end{code}
We need, for |a' = rgArgs gamma Ugg i a|
\begin{code}
ih  :  IndHyp gamma Ugg C a'
    =  (v : IndArg gamma U a') -> C (IndIndex gamma U a' v) (Ind gamma U a' v)
\end{code}
Our intuition is that |eps| does not change the inductive occurrences in any
way, and indeed we can prove the following lemma:

\begin{lemma} \label{lem-eps-Ind}
For any |a : Args (eps gamma i) U| and |v : IndArg (eps gamma i) U a| the
following equalities hold definitionally.
\begin{code}
~
IndArg    gamma U      (rgArgs gamma U i a)    = IndArg    (eps gamma i) U a
IndIndex  gamma U      (rgArgs gamma U i a) v  = IndIndex  (eps gamma i) U a v
Ind       gamma U      (rgArgs gamma U i a) v  = Ind       (eps gamma i) U a v
IndHyp    gamma U C    (rgArgs gamma U i a)    = IndHyp    (eps gamma i) U C a
indHyp    gamma U C g  (rgArgs gamma U i a)    = indHyp    (eps gamma i) U C g a
~
\end{code}
\end{lemma}
%format lem_epsInd = "\ref{lem-eps-Ind}"
\begin{proof}
  The first three are proven by induction on |gamma|. The last two follows from the first three.
\end{proof}

That is, we can use the induction hypothesis we have as it is. Let us now try
to define the elimination rule. We are given
\begin{code}
~
C     :  (i : I) -> Ugg i -> Set
step  :  (a : Args gamma Ugg) -> IndHyp gamma Ugg C a ->
         C (index gamma Ugg a) (introgg a)
i     :  I
u     :  Ugg i
~
\end{code}
and we have to prove |C i u|. To apply the restricted elimination rule
(|elimUreg|) we need an induction step |stepr| of type
\begin{code}
(i : I)(a : Args (eps gamma i) Ugg) ->
IndHyp (eps gamma i) Ugg C a -> C i (intror i a)
\end{code}
As we have observed the induction hypothesis already has the right type, so we attempt to
define
\begin{code}
stepr i a ih = step (rgArgs gamma Ugg i a) ih
\end{code}
The type of |stepr i a ih| is |C (index gamma U ar) (intror (grArgs gamma U
ar))|, where |ar = rgArgs gamma Ugg i a|. Here, the extra elements in |Ugg|
get in the way. Basically we would like the conversion of a constructor
argument from the restricted representation to a generalised argument and back
to be the (definitional) identity. It is easy to see that this is not the case.
For instance, in our |Even| example the argument to the |evenZ'| constructor
is proof |p : zero == zero|. Converting to a generalised argument we
throw away the proof, and converting back we add a proof by reflexivity. But
|p| and |refl| are not definitionally equal. Fortunately they are
propositionally equal, so we can define the following substitution function:

\begin{code}
~
rgArgssubst :  (gamma : OPg I)(U : I -> Set)
               (C : (i : I) -> rArgs (eps gamma) U i -> Set)
               (i : I)(a : rArgs (eps gamma) U i) ->
               (C  (index gamma U (rgArgs gamma U i a))
                   (grArgs gamma U (rgArgs gamma U i a))
               ) -> C i a

rgArgssubst (iota i) U C j < p, star > m =
  elimId i (\ k q -> C k < q, star >) m j p

rgArgssubst (delta A gamma)   U C j < a, b > m = 
  rgArgssubst (gamma a) U (\ i c -> C i < a, c >) j b m

rgArgssubst (delta H i gamma) U C j < g, b > m =
  rgArgssubst gamma U (\ i c -> C i < g, c >) j b m
~
\end{code}
The interesting case is the |iota|-case where we have to prove |C j <p, star>|
from |C i <refl, star>| and |p : i == j|. This is proven using the elimination
rule, |elimId|, for the identity type. Armed with this substitution rule we can
define the elimination rule for a generalised IID:
\begin{code}
~
elimUgg C step i u = elimUreg C stepr i u
  where
    stepr i a ih = rgArgssubst  gamma Ugg (\ i a -> C i (intror i a))
                                i a (step (rgArgs gamma Ugg i a) ih)
~
\end{code}
In our example the elimination rule becomes
\begin{code}
~
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
~
\end{code}
To improve readability we present the application of the elimination rule for
|Even'| using pattern matching and explicit recursion. The call to
|rgArgssubst| is visible in the equality proof eliminations.

\subsection{Equality rule}

So far we have shown that we can represent generalised IID as a restricted IID
and that the elimination rule is still valid. The only thing remaining is to
show that the equality rule is also valid. That is, that we get the same reduction
behaviour for our representation as we would if we extended our system with
generalised IID.

Let us recall the equality rule we have to prove:
\begin{code}
~
elimUgg C step (index γ Ugg a) (introgg a) =
  step a (indHyp γ Ugg C (elimUgg C step) a)
~
\end{code}
The key insight here is that the equality rule does not talk about arbitrary
elements of |Ugg|, but only those that have been constructed using the
introduction rule. This means that we do not have to satisfy any definitional
equalities for elements where the equality proof is not |refl|. So, the main
step in the proof is to prove that |rgArgssubst| is the definitional identity
when the equality proof is |refl|, i.e. when the argument is build using the
|grArgs| function.

\begin{lemma} \label{lem-rgArgsubst}
  For all |gamma|, |U|, |C|, |a : Args gamma U|, and
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
  which is exactly the equality rule for the identity type.
\end{proof}

The final lemma we need before proving the equality rule is that starting with
a generalised constructor argument, converting it to a restricted one, and then
back is the definitional identity. This amounts to adding a reflexivity proof
and then removing it, so it is easy to see that this should be true.

\begin{lemma} \label{lem-arg-is-a}
  For all |gamma|, |U|, and |a : Args gamma U| it holds definitionally that
  |rgArgs gamma U (index gamma U a) (grArgs gamma U a) = a|
\end{lemma}
%format lem_argIsa = "\ref{lem-arg-is-a}"
\begin{proof}
  By induction on |gamma|.
\end{proof}

Now take
\begin{code}
  a   : Args gamma Ugg
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
=  {equality rule for Ureg}
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
~
\end{code}

This concludes the proof that we can faithfully represent generalised IID in
the theory of restricted IID and the intensional identity type.

\section{Conclusions} \label{sec-concl}

This is good stuff.

\bibliographystyle{abbrv}
\bibliography{../../../../bib/pmgrefs}

\end{document}

% vim: et
