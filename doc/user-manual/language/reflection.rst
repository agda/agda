.. _reflection:

**********
Reflection
**********

.. note::
   This section is incomplete.

Builtin types
-------------

Names
~~~~~

The built-in ``QNAME`` type represents quoted names and comes equipped with
equality, ordering and a show function.

::

  postulate Name : Set
  {-# BUILTIN QNAME Name #-}
  primitive primQNameEquality : Name → Name → Bool
  primitive primQNameLess     : Name → Name → Bool
  primitive primShowQName     : Name → String

Name literals are created using the ``quote`` keyword and can appear both in
terms and in patterns

::

  nameOfNat : Name
  nameOfNat = quote Nat

  isNat : Name → Bool
  isNat (quote Nat) = true
  isNat _ = false

Note that the name being quoted must be in scope.

Metavariables
~~~~~~~~~~~~~

Metavariables are represented by the built-in ``AGDAMETA`` type. They have
primitive equality and ordering::

  postulate Meta : Set
  {-# BUILTIN AGDAMETA Meta #-}
  primitive primMetaEquality : Meta → Meta → Bool
  primitive primMetaLess     : Meta → Meta → Bool

Builtin metavariables show up in reflected terms.

Literals
~~~~~~~~

Literals are mapped to the built-in ``AGDALITERAL`` datatype. Given the appropriate
built-in binding for the types ``Nat``, ``Float``, etc, the ``AGDALITERAL`` datatype
has the following shape:

::

    data Literal : Set where
      nat    : Nat    → Literal
      float  : Float  → Literal
      char   : Char   → Literal
      string : String → Literal
      name   : Name   → Literal

    {-# BUILTIN AGDALITERAL   Literal #-}
    {-# BUILTIN AGDALITNAT    nat     #-}
    {-# BUILTIN AGDALITFLOAT  float   #-}
    {-# BUILTIN AGDALITCHAR   char    #-}
    {-# BUILTIN AGDALITSTRING string  #-}
    {-# BUILTIN AGDALITQNAME  name    #-}

Terms
~~~~~

Terms, types and sorts are mapped to the ``AGDATERM``, ``AGDATYPE`` and ``AGDASORT``
respectively. Terms use de Bruijn indices to represent variables.

::

  mutual
    data Term : Set where
      -- Variable (de Bruijn index) applied to arguments.
      var     : (x : Nat) (args : List (Arg Term)) → Term
      -- Constructor applied to arguments.
      con     : (c : Name) (args : List (Arg Term)) → Term
      -- Identifier applied to arguments.
      def     : (f : Name) (args : List (Arg Term)) → Term
      -- Metavariable applied to arguments
      meta    : (x : Name) (args : List (Arg Term)) → Term
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
      -- Anything else. Treated as a fresh metavariable when unquoting.
      unknown : Term

    data Type : Set where
      el : (s : Sort) (t : Term) → Type

    data Sort : Set where
      -- A Set of a given (possibly neutral) level.
      set     : (t : Term) → Sort
      -- A Set of a given concrete level.
      lit     : (n : Nat) → Sort
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
  {-# BUILTIN AGDATERMMETA        meta    #-}
  {-# BUILTIN AGDATERMLAM         lam     #-}
  {-# BUILTIN AGDATERMEXTLAM      pat-lam #-}
  {-# BUILTIN AGDATERMPI          pi      #-}
  {-# BUILTIN AGDATERMSORT        sort    #-}
  {-# BUILTIN AGDATERMLIT         lit     #-}
  {-# BUILTIN AGDATERMUNSUPPORTED unknown #-}
  {-# BUILTIN AGDATYPEEL          el      #-}
  {-# BUILTIN AGDASORTSET         set     #-}
  {-# BUILTIN AGDASORTLIT         lit     #-}
  {-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

Absurd lambdas ``λ ()`` are quoted to extended lambdas with an absurd clause.

The built-in constructors AGDATERMUNSUPPORTED and AGDASORTUNSUPPORTED are
translated to meta variables when unquoting. The sort ``Setω`` is translated
to ``AGDASORTUNSUPPORTED``.

Declarations
~~~~~~~~~~~~

There is a built-in type ``AGDADEFINITION`` representing definitions. Values of
this type is returned by the ``AGDATCMGETDEFINITION`` built-in :ref:`described
below <reflection-tc-monad>`.

::

  data FunDef : Set where
    funDef : Type → List Clause → FunDef

  {-# BUILTIN AGDAFUNDEF    FunDef #-}
  {-# BUILTIN AGDAFUNDEFCON funDef #-}

  postulate
    DataDef   : Set
    RecordDef : Set

  {-# BUILTIN AGDADATADEF   DataDef   #-}
  {-# BUILTIN AGDARECORDDEF RecordDef #-}

  data Definition : Set where
    funDef          : FunDef    → Definition
    dataDef         : DataDef   → Definition
    recordDef       : RecordDef → Definition
    dataConstructor : Definition
    axiom           : Definition
    prim            : Definition

  {-# BUILTIN AGDADEFINITION                Definition      #-}
  {-# BUILTIN AGDADEFINITIONFUNDEF          funDef          #-}
  {-# BUILTIN AGDADEFINITIONDATADEF         dataDef         #-}
  {-# BUILTIN AGDADEFINITIONRECORDDEF       recordDef       #-}
  {-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR dataConstructor #-}
  {-# BUILTIN AGDADEFINITIONPOSTULATE       axiom           #-}
  {-# BUILTIN AGDADEFINITIONPRIMITIVE       prim            #-}

The built-in ``AGDADATADEF`` type can be used to get the constructors and number
of parameters to a datatype using the appropriate operations in the :ref:`TC
monad <reflection-tc-monad>`.

.. _reflection-tc-monad:

Type checking computations
~~~~~~~~~~~~~~~~~~~~~~~~~~

Metaprograms, i.e. programs that create other programs, run in a built-in type
checking monad ``TC``::

  postulate
    TC         : ∀ {a} → Set a → Set a
    returnTC   : ∀ {a} {A : Set a} → A → TC A
    bindTC     : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B

  {-# BUILTIN AGDATCM       TC       #-}
  {-# BUILTIN AGDATCMRETURN returnTC #-}
  {-# BUILTIN AGDATCMBIND   bindTC   #-}

The ``TC`` monad provides an interface to the Agda type checker using the
following primitive operations::

  postulate
    -- Unify two terms, potentially solving metavariables in the process.
    unify : Term → Term → TC ⊤

    -- Create a fresh metavariable of the given type. The metavariable can
    -- depend on variables in the current context.
    newMeta : Type → TC Term

    -- Throw a type error. Can be caught by catchTC.
    typeError : ∀ {a} {A : Set a} → String → TC A

    -- Block a type checking computation on a metavariable. This will abort
    -- the computation and restart it (from the beginning) when the
    -- metavariable is solved.
    blockOnMeta : ∀ {a} {A : Set a} → Meta → TC A

    -- Backtrack and try the second argument if the first argument throws a
    -- type error.
    catchTC : ∀ {a} {A : Set a} → TC A → TC A → TC A

    -- Infer the type of a given term
    inferType : Term → TC Type

    -- Check a term against a given type. This may resolve implicit arguments
    -- in the term, so a new refined term is returned.
    checkType : Term → Type → TC Term

    -- Compute the normal form of a term.
    normalise : Term → TC Term

    -- Get the current context.
    getContext : TC (List (Arg Type))

    -- Extend the current context with a variable of the given type.
    extendContext : ∀ {a} {A : Set a} → Arg Type → TC A → TC A

    -- Set the current context.
    inContext : ∀ {a} {A : Set a} → List (Arg Type) → TC A → TC A

    -- Create a fresh name.
    freshName : String → TC QName

    -- Declare a new function of the given type. The function must be defined
    -- later using 'defineFun'.
    declareDef : QName → Type → TC ⊤

    -- Define a declared function. The function may have been declared using
    -- 'declareDef' or with an explicit type signature in the program.
    defineFun : QName → List Clause → TC ⊤

    -- Get the type of a defined name. Replaces 'primQNameType'.
    getType : QName → TC Type

    -- Get the definition of a defined name. Replaces 'primQNameDefinition'.
    getDefinition : QName → TC Definition

    -- Get the number of parameters of a data type. Replaces 'primDataNumberOfParameters'.
    numberOfParameters : DataDef → TC Nat

    -- Get the constructors of a datatype. Replaces 'primDataConstructors'.
    getConstructors : DataDef   → TC (List QName)

  {-# BUILTIN AGDATCMUNIFY              unify              #-}
  {-# BUILTIN AGDATCMNEWMETA            newMeta            #-}
  {-# BUILTIN AGDATCMTYPEERROR          typeError          #-}
  {-# BUILTIN AGDATCMBLOCKONMETA        blockOnMeta        #-}
  {-# BUILTIN AGDATCMCATCHERROR         catchTC            #-}
  {-# BUILTIN AGDATCMINFERTYPE          inferType          #-}
  {-# BUILTIN AGDATCMCHECKTYPE          checkType          #-}
  {-# BUILTIN AGDATCMNORMALISE          normalise          #-}
  {-# BUILTIN AGDATCMGETCONTEXT         getContext         #-}
  {-# BUILTIN AGDATCMEXTENDCONTEXT      extendContext      #-}
  {-# BUILTIN AGDATCMINCONTEXT          inContext          #-}
  {-# BUILTIN AGDATCMFRESHNAME          freshName          #-}
  {-# BUILTIN AGDATCMDECLAREDEF         declareDef         #-}
  {-# BUILTIN AGDATCMDEFINEFUN          defineFun          #-}
  {-# BUILTIN AGDATCMGETTYPE            getType            #-}
  {-# BUILTIN AGDATCMGETDEFINITION      getDefinition      #-}
  {-# BUILTIN AGDATCMNUMBEROFPARAMETERS numberOfParameters #-}
  {-# BUILTIN AGDATCMGETCONSTRUCTORS    getConstructors    #-}

Metaprogramming
---------------

There are three ways to run a metaprogram (``TC`` computation). To run a
metaprogram in a term position you use a `macro <macros_>`_. To run
metaprograms to create top-level definitions you can use the ``unquoteDecl``
and ``unquoteDef`` primitives (see `Unquoting Declarations`_).

.. _macros:

Macros
~~~~~~

Macros are functions of type ``t₁ → t₂ → .. → Term → TC ⊤`` that are defined in
a ``macro`` block. The last argument is supplied by the type checker and will
be the representation of a metavariable that should be instantiated with the
result of the macro.

Macro application is guided by the type of the macro, where ``Term`` and
``Name`` arguments are quoted before passed to the macro.  Arguments of any
other type are preserved as-is.

For example, the macro application ``f u v w`` where
``f : Term → Name → Bool → Term → TC ⊤`` desugars into::

  unquote (f (quoteTerm u) (quote v) w)

where ``quoteTerm u`` takes a ``u`` of arbitrary type and returns its
representation in the ``Term`` data type, and ``unquote m`` runs a computation
in the ``TC`` monad. Specifically, when checking ``unquote m : A`` for some
type ``A`` the type checker proceeds as follows:

  - Check ``m : Term → TC ⊤``.
  - Create a fresh metavariable ``hole : A``.
  - Let ``qhole : Term`` be the quoted representation of ``hole``.
  - Execute ``m qhole``.
  - Return (the now hopefully instantiated) ``hole``.

.. note::
   The ``quoteTerm`` and ``unquote`` primitives are available in the language,
   but it is recommended to avoid using them in favour of macros.

Limitations:

  - Macros cannot be recursive. This can be worked around by defining the
    recursive function outside the macro block and have the macro call the
    recursive function.

Silly example:

::

    macro
      plus-to-times : Term → Term → TC ⊤
      plus-to-times (def (quote _+_) (a ∷ b ∷ [])) hole = unify hole (def (quote _*_) (a ∷ b ∷ []))
      plus-to-times v hole = unify hole v

    thm : (a b : Nat) → plus-to-times (a + b) ≡ a * b
    thm a b = refl

Macros lets you write tactics that can be applied without any syntactic
overhead. For instance, suppose you have a solver::

  magic : Type → Term

that takes a reflected goal and outputs a proof (when successful). You can then
define the following macro::

  macro
    by-magic : Term → TC ⊤
    by-magic hole =
      bindTC (inferType hole) λ goal →
      unify hole (magic goal)

This lets you apply the magic tactic as a normal function::

  thm : ¬ P ≡ NP
  thm = by-magic

Unquoting Declarations
~~~~~~~~~~~~~~~~~~~~~~

While macros let you write metaprograms to create terms, it is also useful to
be able to create top-level definitions. You can do this from a macro using the
``declareDef`` and ``defineFun`` primitives, but there is no way to bring such
definitions into scope. For this purpose there are two top-level primitives
``unquoteDecl`` and ``unquoteDef`` that runs a ``TC`` computation in a
declaration position. They both have the same form::

  unquoteDecl x₁ .. xₙ = m
  unquoteDef  x₁ .. xₙ = m

except that the list of names can be empty for ``unquoteDecl``, but not for
``unquoteDef``. In both cases ``m`` should have type ``TC ⊤``. The main
difference between the two is that ``unquoteDecl`` requires ``m`` to both
declare (with ``declareDef``) and define (with ``defineFun``) the ``xᵢ``
whereas ``unquoteDef`` expects the ``xᵢ`` to be already declared. In other
words, ``unquoteDecl`` brings the ``xᵢ`` into scope, but ``unquoteDef``
requires them to already be in scope.

In ``m`` the ``xᵢ`` stand for the names of the functions being defined (i.e.
``xᵢ : Name``) rather than the actual functions.

One advantage of unquoteDef over unquoteDecl is that unquoteDef is allowed in
mutual blocks, allowing mutually recursion between generated definitions and
hand-written definitions.

Examples
--------

Coming soon.
