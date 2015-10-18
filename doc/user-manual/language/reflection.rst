.. _reflection:

**********
Reflection
**********

.. note::
   This section is not yet finished and may contain outdated material!

Builtin types
-------------

Literals
~~~~~~~~

The Term data type ``AGDATERM`` now needs an additional constructor ``AGDATERMLIT``
taking a reflected literal defined as follows (with appropriate builtin
bindings for the types ``Nat``, ``Float``, etc).

::

    data Literal : Set where
      nat    : Nat    → Literal
      float  : Float  → Literal
      char   : Char   → Literal
      string : String → Literal
      qname  : QName  → Literal

    {-# BUILTIN AGDALITERAL   Literal #-}
    {-# BUILTIN AGDALITNAT    nat     #-}
    {-# BUILTIN AGDALITFLOAT  float   #-}
    {-# BUILTIN AGDALITCHAR   char    #-}
    {-# BUILTIN AGDALITSTRING string  #-}
    {-# BUILTIN AGDALITQNAME  qname   #-}

When quoting (``quoteGoal`` or ``quoteTerm``) literals will be mapped to the
``AGDATERMLIT`` constructor. Previously natural number literals were quoted
to suc/zero application and other literals were quoted to
``AGDATERMUNSUPPORTED``.

Terms
~~~~~

The ``Term``, ``Type`` and ``Sort`` datatype:

::

  mutual
    data Term : Set where
      -- Variable applied to arguments.
      var     : (x : ℕ) (args : List (Arg Term)) → Term
      -- Constructor applied to arguments.
      con     : (c : Name) (args : List (Arg Term)) → Term
      -- Identifier applied to arguments.
      def     : (f : Name) (args : List (Arg Term)) → Term
      -- Different kinds of λ-abstraction.
      lam     : (v : Visibility) (t : Abs Term) → Term
      -- Pattern matching λ-abstraction.
      pat-lam : (cs : List Clause) (args : List (Arg Term)) → Term
      -- Pi-type.
      pi      : (t₁ : Arg Type) (t₂ : Abs Type) → Term
      -- A sort.
      sort    : (s : Sort) → Term
      -- A literal.
      lit     : (l : Literal) → Term
      -- Reflection constructions.
      quote-goal : (t : Abs Term) → Term
      quote-term : (t : Term) → Term
      quote-context : Term
      unquote-term : (t : Term) (args : List (Arg Term)) → Term
      -- Anything else.
      unknown : Term

    data Type : Set where
      el : (s : Sort) (t : Term) → Type

    data Sort : Set where
      -- A Set of a given (possibly neutral) level.
      set     : (t : Term) → Sort
      -- A Set of a given concrete level.
      lit     : (n : ℕ) → Sort
      -- Anything else.
      unknown : Sort

    data Clause : Set where
      clause        : (pats : List (Arg Pattern))(body : Term) → Clause
      absurd-clause : (pats : List (Arg Pattern)) → Clause

  {-# BUILTIN AGDASORT    Sort    #-}
  {-# BUILTIN AGDATYPE    Type    #-}
  {-# BUILTIN AGDATERM    Term    #-}
  {-# BUILTIN AGDACLAUSE  Clause  #-}

  {-# BUILTIN AGDATERMVAR         var     #-}
  {-# BUILTIN AGDATERMCON         con     #-}
  {-# BUILTIN AGDATERMDEF         def     #-}
  {-# BUILTIN AGDATERMLAM         lam     #-}


Absurd lambdas ``(λ ())`` are quoted to extended lambdas with an absurd clause.

Meta variables
~~~~~~~~~~~~~~

The builtin constructors AGDATERMUNSUPPORTED and AGDASORTUNSUPPORTED are now
translated to meta variables when unquoting.

Levels
~~~~~~

Universe levels are now quoted properly instead of being quoted to
AGDASORTUNSUPPORTED. Setω  still gets an unsupported sort, however.

Function Definitions
~~~~~~~~~~~~~~~~~~~~

AGDAFUNDEF should now map to a data type defined as follows:

::

    data Pattern : Set where
      con    : QName → List (Arg Pattern) → Pattern
      dot    : Pattern
      var    : Pattern
      lit    : Literal → Pattern
      proj   : QName → Pattern
      absurd : Pattern

    {-# BUILTIN AGDAPATTERN   Pattern #-}
    {-# BUILTIN AGDAPATCON    con     #-}
    {-# BUILTIN AGDAPATDOT    dot     #-}
    {-# BUILTIN AGDAPATVAR    var     #-}
    {-# BUILTIN AGDAPATLIT    lit     #-}
    {-# BUILTIN AGDAPATPROJ   proj    #-}
    {-# BUILTIN AGDAPATABSURD absurd  #-}

    data Clause : Set where
      clause        : List (Arg Pattern) → Term → Clause
      absurd-clause : List (Arg Pattern) → Clause

    {-# BUILTIN AGDACLAUSE       Clause        #-}
    {-# BUILTIN AGDACLAUSECLAUSE clause        #-}
    {-# BUILTIN AGDACLAUSEABSURD absurd-clause #-}

    data FunDef : Set where
      fun-def : Type → List Clause → FunDef

    {-# BUILTIN AGDAFUNDEF    FunDef  #-}
    {-# BUILTIN AGDAFUNDEFCON fun-def #-}


Quoting and Unquoting
---------------------

Unquoting
~~~~~~~~~

The construction "unquote t" converts a representation of an Agda term
to actual Agda code in the following way:

1. The argument t must have type Term (see the reflection API above).

2. The argument is normalised.

3. The entire construction is replaced by the normal form, which is
   treated as syntax written by the user and type-checked in the
   usual way.

Examples:

::

    test : unquote (def (quote ℕ) []) ≡ ℕ
    test = refl

    id : (A : Set) → A → A
    id = unquote (lam visible (lam visible (var 0 [])))

    id-ok : id ≡ (λ A (x : A) → x)
    id-ok = refl


Quoting Terms
~~~~~~~~~~~~~

The construction "quoteTerm t" is similar to "quote n", but whereas
quote is restricted to names n, quoteTerm accepts terms t. The
construction is handled in the following way:

1. The type of t is inferred. The term t must be type-correct.

2. The term t is normalised.

3. The construction is replaced by the Term representation (see the
   reflection API above) of the normal form. Any unsolved metavariables
   in the term are represented by the "unknown" term constructor.

Examples:

::

    test₁ : quoteTerm (λ {A : Set} (x : A) → x) ≡
            lam hidden (lam visible (var 0 []))
    test₁ = refl

    -- Local variables are represented as de Bruijn indices.
    test₂ : (λ {A : Set} (x : A) → quoteTerm x) ≡ (λ x → var 0 [])
    test₂ = refl

    -- Terms are normalised before being quoted.
    test₃ : quoteTerm (0 + 0) ≡ con (quote zero) []


Quote Patterns
~~~~~~~~~~~~~~

For instance, here is a function that unquotes a (closed) natural number
term.

::

    unquoteNat : Term → Maybe Nat
    unquoteNat (con (quote Nat.zero) [])            = just zero
    unquoteNat (con (quote Nat.suc) (arg _ n ∷ [])) = fmap suc (unquoteNat n)
    unquoteNat _                                    = nothing



Unquoting Declarations
~~~~~~~~~~~~~~~~~~~~~~

You can now define (recursive) functions by reflection using the new
unquoteDecl declaration

::

    unquoteDecl x = e

Here e should have type AGDAFUNDEF and evaluate to a closed value. This value
is then spliced in as the definition of x. In the body e, x has type QNAME
which lets you splice in recursive definitions.

Standard modifiers, such as fixity declarations, can be applied to x as
expected.

Quoting Goals
~~~~~~~~~~~~~

  - quoteGoal x in e

    In e the value of x will be a representation of the goal type
    (the type expected of the whole expression) as an element in a
    datatype of Agda terms (see below). For instance,

::

      example : ℕ
      example = quoteGoal x in {! at this point x = def (quote ℕ) [] !}

Quoting Terms
~~~~~~~~~~~~~

  - quote x : Name

    If x is the name of a definition (function, datatype, record, or
    a constructor), quote x gives you the representation of x as a
    value in the primitive type Name (see below).

Quoted terms use the following BUILTINs and primitives (available
from the standard library module Reflection):

::

    -- The type of Agda names.

    postulate Name : Set

    {-# BUILTIN QNAME Name #-}

    primitive primQNameEquality : Name → Name → Bool

    -- Arguments.

    Explicit? = Bool

    data Arg A : Set where
      arg : Explicit? → A → Arg A

    {-# BUILTIN ARG    Arg #-}
    {-# BUILTIN ARGARG arg #-}

    -- The type of Agda terms.

    data Term : Set where
      var     : ℕ → List (Arg Term) → Term
      con     : Name → List (Arg Term) → Term
      def     : Name → List (Arg Term) → Term
      lam     : Explicit? → Term → Term
      pi      : Arg Term → Term → Term
      sort    : Term
      unknown : Term

Tactics
-------

New syntactic sugar 'tactic e' and 'tactic e | e1 | .. | en'.

It desugars as follows and makes it less unwieldy to call reflection-based
tactics.

::

    tactic e                --> quoteGoal g in unquote (e g)
    tactic e | e1 | .. | en --> quoteGoal g in unquote (e g) e1 .. en

Note that in the second form the tactic function should generate a function
from a number of new subgoals to the original goal. The type of e should be
Term -> Term in both cases.


Macros
------

Macros are functions of type t1 → t2 → .. → Term that are defined in a 'macro'
block. Macro application is guided by the type of the macro, where Term
arguments desugar into the 'quoteTerm' syntax and Name arguments into the
'quote' syntax. Arguments of any other type are preserved as-is.

For example, the macro application 'f u v w' where the macro
f has the type 'Term → Name → Bool → Term' desugars into
'unquote (f (quoteTerm u) (quote v) w)'

Limitations:

  - Macros cannot be recursive. This can be worked around by defining the
    recursive function outside the macro block and have the macro call the
    recursive function.

Silly example:

::

    macro
      plus-to-times : Term -> Term
      plus-to-times (def (quote _+_) (a ∷ b ∷ [])) = def (quote _*_) (a ∷ b ∷ [])
      plus-to-times v = v

    thm : (a b : Nat) → plus-to-times (a + b) ≡ a * b
    thm a b = refl


Macros are most useful when writing tactics, since they let you hide the
reflection machinery. For instance, suppose you have a solver

::

    magic : Term → Term

that takes a reflected goal and outputs a proof (when successful). You can
then use the tactic function from above to define

::

    macro
      by-magic : Term
      by-magic = `tactic (quote magic)

This lets you apply the magic tactic without any syntactic noise at all:

::

    thm : ¬ P ≡ NP
    thm = by-magic

