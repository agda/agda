.. _reflection:

**********
Reflection
**********

.. note::
   This section is incomplete.

Builtin types
-------------

Literals
~~~~~~~~

Literals are mapped to the builtin ``AGDALITERAL`` datatype. Given the appropriate
builtin binding for the types ``Nat``, ``Float``, etc, the ``AGDALITERAL`` datatype
has the following shape:

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

Terms
~~~~~

Terms, types and sorts are mapped to the ``AGDATERM``, ``AGDATYPE`` and ``AGDASORT``
respectively. Terms use a locally-nameless representation using de Bruijn indices.


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

  {-# BUILTIN AGDATERMVAR         var     #-}
  {-# BUILTIN AGDATERMCON         con     #-}
  {-# BUILTIN AGDATERMDEF         def     #-}
  {-# BUILTIN AGDATERMLAM         lam     #-}
  {-# BUILTIN AGDATERMEXTLAM      pat-lam #-}
  {-# BUILTIN AGDATERMPI          pi      #-}
  {-# BUILTIN AGDATERMSORT        sort    #-}
  {-# BUILTIN AGDATERMLIT         lit     #-}
  {-# BUILTIN AGDATERMQUOTETERM    quote-term    #-}
  {-# BUILTIN AGDATERMQUOTEGOAL    quote-goal    #-}
  {-# BUILTIN AGDATERMQUOTECONTEXT quote-context #-}
  {-# BUILTIN AGDATERMUNQUOTE      unquote-term  #-}
  {-# BUILTIN AGDATERMUNSUPPORTED unknown #-}
  {-# BUILTIN AGDATYPEEL          el      #-}
  {-# BUILTIN AGDASORTSET         set     #-}
  {-# BUILTIN AGDASORTLIT         lit     #-}
  {-# BUILTIN AGDASORTUNSUPPORTED unknown #-}


Absurd lambdas ``(λ ())`` are quoted to extended lambdas with an absurd clause.

The builtin constructors AGDATERMUNSUPPORTED and AGDASORTUNSUPPORTED are
translated to meta variables when unquoting. The sort Setω is translated
to ``AGDASORTUNSUPPORTED``.

Function Definitions
~~~~~~~~~~~~~~~~~~~~

Functions definitions are mapped to the ``AGDAFUNDEF`` builtin:

::

  -- Function definition.
  data FunctionDef : Set where
    fun-def : Type → Clauses → FunctionDef

  {-# BUILTIN AGDAFUNDEF    FunctionDef #-}
  {-# BUILTIN AGDAFUNDEFCON fun-def     #-}


Quoting and Unquoting
---------------------

Unquoting Terms
~~~~~~~~~~~~~~~

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


Unquoting Declarations
~~~~~~~~~~~~~~~~~~~~~~

You can define (recursive) functions by reflection using the new
unquoteDecl declaration:

::

    unquoteDecl x = e

Here e should have type AGDAFUNDEF and evaluate to a closed value. This value
is then spliced in as the definition of x. In the body e, x has type QNAME
which lets you splice in recursive definitions.

Standard modifiers, such as fixity declarations, can be applied to x as
expected.

Quoting Terms
~~~~~~~~~~~~~

The construction "quoteTerm t" evaluates to the ``AGDATERM``
representation of the term t. This is done in the following way:

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


Quoting Names
~~~~~~~~~~~~~

The "quote x" expression returns the builtin ``QNAME`` representation
of the given name.

::

  test : Name
  test = quote ℕ


Quoting Goals
~~~~~~~~~~~~~

The "quoteGoal x in e" construct allows inspecting the current goal type
(the type expected of the whole expression):

::

      example : ℕ
      example = quoteGoal x in {! at this point x = def (quote ℕ) [] !}





Quote Patterns
~~~~~~~~~~~~~~

Quote patterns allow pattern matching on quoted names.
For instance, here is a function that unquotes a (closed) natural number
term:

::

    unquoteNat : Term → Maybe Nat
    unquoteNat (con (quote Nat.zero) [])            = just zero
    unquoteNat (con (quote Nat.suc) (arg _ n ∷ [])) = fmap suc (unquoteNat n)
    unquoteNat _                                    = nothing

Tactics
-------

Tactis are syntactic sugar which allow using reflection in a syntactically
lightweigt manner. It desugars as follows:

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

