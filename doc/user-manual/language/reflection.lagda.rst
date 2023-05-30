..
  ::
  module language.reflection where

  open import Agda.Builtin.Sigma
  open import Agda.Builtin.Unit
  open import Agda.Builtin.Nat
  open import Agda.Builtin.List
  open import Agda.Builtin.Float
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Char
  open import Agda.Builtin.String
  open import Agda.Builtin.Word
  open import Agda.Builtin.Equality
  open import Agda.Primitive

  data ⊥ : Set where

  pattern [_] x = x ∷ []

  ¬_ : ∀ {u} → Set u → Set u
  ¬ x  = x → ⊥

  infixl 2 ¬_

  data Associativity : Set where
    left-assoc  : Associativity
    right-assoc : Associativity
    non-assoc   : Associativity

  data Precedence : Set where
    related   : Float → Precedence
    unrelated : Precedence

  data Fixity : Set where
    fixity : Associativity → Precedence → Fixity

  {-# BUILTIN ASSOC      Associativity #-}
  {-# BUILTIN ASSOCLEFT  left-assoc    #-}
  {-# BUILTIN ASSOCRIGHT right-assoc   #-}
  {-# BUILTIN ASSOCNON   non-assoc     #-}

  {-# BUILTIN PRECEDENCE    Precedence #-}
  {-# BUILTIN PRECRELATED   related    #-}
  {-# BUILTIN PRECUNRELATED unrelated  #-}

  {-# BUILTIN FIXITY       Fixity #-}
  {-# BUILTIN FIXITYFIXITY fixity #-}

.. _reflection:

**********
Reflection
**********

Builtin types
-------------

Names
~~~~~

The built-in ``QNAME`` type represents quoted names and comes equipped with
equality, ordering, and a show function.

::

  postulate Name : Set
  {-# BUILTIN QNAME Name #-}

  primitive
    primQNameEquality : Name → Name → Bool
    primQNameLess     : Name → Name → Bool
    primShowQName     : Name → String

The fixity of a name can also be retrived.

::

  primitive
    primQNameFixity    : Name → Fixity

To define a decidable propositional equality with the option
:option:`--safe`, one can use the conversion to a pair of built-in
64-bit machine words

::

  primitive
    primQNameToWord64s : Name → Σ Word64 (λ _ → Word64)

with the injectivity proof in the ``Properties`` module.::

  primitive
    primQNameToWord64sInjective : ∀ a b → primQNameToWord64s a ≡ primQNameToWord64s b → a ≡ b


Name literals are created using the ``quote`` keyword and can appear both in
terms and in patterns

::

  nameOfNat : Name
  nameOfNat = quote Nat

  isNat : Name → Bool
  isNat (quote Nat) = true
  isNat _           = false

Note that the name being quoted must be in scope.

Metavariables
~~~~~~~~~~~~~

Metavariables are represented by the built-in ``AGDAMETA`` type. They have
primitive equality, ordering, show, and conversion to Nat::

  postulate Meta : Set
  {-# BUILTIN AGDAMETA Meta #-}

  primitive
    primMetaEquality : Meta → Meta → Bool
    primMetaLess     : Meta → Meta → Bool
    primShowMeta     : Meta → String
    primMetaToNat    : Meta → Nat

Builtin metavariables show up in reflected terms. In ``Properties``, there is a proof of injectivity
of ``primMetaToNat``

::

  primitive
    primMetaToNatInjective : ∀ a b → primMetaToNat a ≡ primMetaToNat b → a ≡ b

which can be used to define a decidable propositional equality with
the option :option:`--safe`.

Literals
~~~~~~~~

Literals are mapped to the built-in ``AGDALITERAL`` datatype. Given the appropriate
built-in binding for the types ``Nat``, ``Float``, etc, the ``AGDALITERAL`` datatype
has the following shape::

  data Literal : Set where
    nat    : (n : Nat)    → Literal
    word64 : (n : Word64) → Literal
    float  : (x : Float)  → Literal
    char   : (c : Char)   → Literal
    string : (s : String) → Literal
    name   : (x : Name)   → Literal
    meta   : (x : Meta)   → Literal

  {-# BUILTIN AGDALITERAL   Literal #-}
  {-# BUILTIN AGDALITNAT    nat     #-}
  {-# BUILTIN AGDALITWORD64 word64  #-}
  {-# BUILTIN AGDALITFLOAT  float   #-}
  {-# BUILTIN AGDALITCHAR   char    #-}
  {-# BUILTIN AGDALITSTRING string  #-}
  {-# BUILTIN AGDALITQNAME  name    #-}
  {-# BUILTIN AGDALITMETA   meta    #-}

Arguments
~~~~~~~~~

Arguments can be (visible), {hidden}, or {{instance}}::

  data Visibility : Set where
    visible hidden instance′ : Visibility

  {-# BUILTIN HIDING   Visibility #-}
  {-# BUILTIN VISIBLE  visible    #-}
  {-# BUILTIN HIDDEN   hidden     #-}
  {-# BUILTIN INSTANCE instance′  #-}

Arguments can be relevant or irrelevant::

  data Relevance : Set where
    relevant irrelevant : Relevance

  {-# BUILTIN RELEVANCE  Relevance  #-}
  {-# BUILTIN RELEVANT   relevant   #-}
  {-# BUILTIN IRRELEVANT irrelevant #-}

Arguments also have a quantity::

  data Quantity : Set where
    quantity-0 quantity-ω : Quantity

  {-# BUILTIN QUANTITY   Quantity   #-}
  {-# BUILTIN QUANTITY-0 quantity-0 #-}
  {-# BUILTIN QUANTITY-ω quantity-ω #-}

Relevance and quantity are combined into a modality::

  data Modality : Set where
    modality : (r : Relevance) (q : Quantity) → Modality

  {-# BUILTIN MODALITY             Modality #-}
  {-# BUILTIN MODALITY-CONSTRUCTOR modality #-}

The visibility and the modality characterise the behaviour of an
argument::

  data ArgInfo : Set where
    arg-info : (v : Visibility) (m : Modality) → ArgInfo

  data Arg (A : Set) : Set where
    arg : (i : ArgInfo) (x : A) → Arg A

  {-# BUILTIN ARGINFO    ArgInfo  #-}
  {-# BUILTIN ARGARGINFO arg-info #-}
  {-# BUILTIN ARG        Arg      #-}
  {-# BUILTIN ARGARG     arg      #-}


Name abstraction
~~~~~~~~~~~~~~~~

::

  data Abs (A : Set) : Set where
    abs : (s : String) (x : A) → Abs A

  {-# BUILTIN ABS    Abs #-}
  {-# BUILTIN ABSABS abs #-}

Terms
~~~~~

Terms, sorts, patterns, and clauses are mutually recursive and mapped
to the ``AGDATERM``, ``AGDASORT``, ``AGDAPATTERN`` and ``AGDACLAUSE``
built-ins respectively. Types are simply terms. Terms and patterns use
de Bruijn indices to represent variables.

::

  data Term : Set
  data Sort : Set
  data Pattern : Set
  data Clause : Set
  Type = Term
  Telescope = List (Σ String λ _ → Arg Type)

  data Term where
    var       : (x : Nat) (args : List (Arg Term)) → Term
    con       : (c : Name) (args : List (Arg Term)) → Term
    def       : (f : Name) (args : List (Arg Term)) → Term
    lam       : (v : Visibility) (t : Abs Term) → Term
    pat-lam   : (cs : List Clause) (args : List (Arg Term)) → Term
    pi        : (a : Arg Type) (b : Abs Type) → Term
    agda-sort : (s : Sort) → Term
    lit       : (l : Literal) → Term
    meta      : (x : Meta) → List (Arg Term) → Term
    unknown   : Term -- Treated as '_' when unquoting.

  data Sort where
    set     : (t : Term) → Sort -- A Set of a given (possibly neutral) level.
    lit     : (n : Nat) → Sort  -- A Set of a given concrete level.
    prop    : (t : Term) → Sort -- A Prop of a given (possibly neutral) level.
    propLit : (n : Nat) → Sort  -- A Prop of a given concrete level.
    inf     : (n : Nat) → Sort  -- Setωi of a given concrete level i.
    unknown : Sort

  data Pattern where
    con    : (c : Name) (ps : List (Arg Pattern)) → Pattern
    dot    : (t : Term)    → Pattern
    var    : (x : Nat   )  → Pattern
    lit    : (l : Literal) → Pattern
    proj   : (f : Name)    → Pattern
    absurd : (x : Nat)     → Pattern  -- Absurd patterns have de Bruijn indices

  data Clause where
    clause        : (tel : Telescope) (ps : List (Arg Pattern)) (t : Term) → Clause
    absurd-clause : (tel : Telescope) (ps : List (Arg Pattern)) → Clause

  {-# BUILTIN AGDATERM    Term   #-}
  {-# BUILTIN AGDASORT    Sort   #-}
  {-# BUILTIN AGDAPATTERN Pattern #-}
  {-# BUILTIN AGDACLAUSE  Clause #-}

  {-# BUILTIN AGDATERMVAR         var       #-}
  {-# BUILTIN AGDATERMCON         con       #-}
  {-# BUILTIN AGDATERMDEF         def       #-}
  {-# BUILTIN AGDATERMMETA        meta      #-}
  {-# BUILTIN AGDATERMLAM         lam       #-}
  {-# BUILTIN AGDATERMEXTLAM      pat-lam   #-}
  {-# BUILTIN AGDATERMPI          pi        #-}
  {-# BUILTIN AGDATERMSORT        agda-sort #-}
  {-# BUILTIN AGDATERMLIT         lit       #-}
  {-# BUILTIN AGDATERMUNSUPPORTED unknown   #-}

  {-# BUILTIN AGDASORTSET         set     #-}
  {-# BUILTIN AGDASORTLIT         lit     #-}
  {-# BUILTIN AGDASORTPROP        prop    #-}
  {-# BUILTIN AGDASORTPROPLIT     propLit #-}
  {-# BUILTIN AGDASORTINF         inf     #-}
  {-# BUILTIN AGDASORTUNSUPPORTED unknown #-}

  {-# BUILTIN AGDAPATCON    con     #-}
  {-# BUILTIN AGDAPATDOT    dot     #-}
  {-# BUILTIN AGDAPATVAR    var     #-}
  {-# BUILTIN AGDAPATLIT    lit     #-}
  {-# BUILTIN AGDAPATPROJ   proj    #-}
  {-# BUILTIN AGDAPATABSURD absurd  #-}

  {-# BUILTIN AGDACLAUSECLAUSE clause        #-}
  {-# BUILTIN AGDACLAUSEABSURD absurd-clause #-}

Absurd lambdas ``λ ()`` are quoted to extended lambdas with an absurd clause.

The built-in constructors ``AGDATERMUNSUPPORTED`` and ``AGDASORTUNSUPPORTED``
are translated to meta variables when unquoting.

Declarations
~~~~~~~~~~~~

There is a built-in type ``AGDADEFINITION`` representing definitions. Values of
this type is returned by the ``AGDATCMGETDEFINITION`` built-in :ref:`described
below <reflection-tc-monad>`.

::

  data Definition : Set where
    function    : (cs : List Clause) → Definition
    data-type   : (pars : Nat) (cs : List Name) → Definition  -- parameters and constructors
    record-type : (c : Name) (fs : List (Arg Name)) →         -- c: name of record constructor
                  Definition                                  -- fs: fields
    data-cons   : (d : Name) → Definition                     -- d: name of data type
    axiom       : Definition
    prim-fun    : Definition

  {-# BUILTIN AGDADEFINITION                Definition  #-}
  {-# BUILTIN AGDADEFINITIONFUNDEF          function    #-}
  {-# BUILTIN AGDADEFINITIONDATADEF         data-type   #-}
  {-# BUILTIN AGDADEFINITIONRECORDDEF       record-type #-}
  {-# BUILTIN AGDADEFINITIONDATACONSTRUCTOR data-cons   #-}
  {-# BUILTIN AGDADEFINITIONPOSTULATE       axiom       #-}
  {-# BUILTIN AGDADEFINITIONPRIMITIVE       prim-fun    #-}

Type errors
~~~~~~~~~~~

Type checking computations (see :ref:`below <reflection-tc-monad>`)
can fail with an error, which is a list of ``ErrorPart``\s. This
allows metaprograms to generate nice errors without having to
implement pretty printing for reflected terms.

::

  -- Error messages can contain embedded names and terms.
  data ErrorPart : Set where
    strErr  : String → ErrorPart
    termErr : Term → ErrorPart
    pattErr : Pattern → ErrorPart
    nameErr : Name → ErrorPart

  {-# BUILTIN AGDAERRORPART       ErrorPart #-}
  {-# BUILTIN AGDAERRORPARTSTRING strErr    #-}
  {-# BUILTIN AGDAERRORPARTTERM   termErr   #-}
  {-# BUILTIN AGDAERRORPARTNAME   nameErr   #-}

Blockers
~~~~~~~~

A blocker represents a set of metavariables that impedes the progress of
a reflective computation. Using a blocker containing all the metas in
(for example) a term traversed by a macro is a lot more efficient than
blocking on individual metas as they are encountered.

::

  data Blocker : Set where
    blockerAny  : List Blocker → Blocker
    blockerAll  : List Blocker → Blocker
    blockerMeta : Meta → Blocker

  {-# BUILTIN AGDABLOCKER     Blocker #-}
  {-# BUILTIN AGDABLOCKERANY  blockerAny #-}
  {-# BUILTIN AGDABLOCKERALL  blockerAll #-}
  {-# BUILTIN AGDABLOCKERMETA blockerMeta #-}

.. _reflection-tc-monad:

Type checking computations
~~~~~~~~~~~~~~~~~~~~~~~~~~

Metaprograms, i.e. programs that create other programs, run in a built-in type
checking monad ``TC``::

  postulate
    TC       : ∀ {a} → Set a → Set a
    returnTC : ∀ {a} {A : Set a} → A → TC A
    bindTC   : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B

  {-# BUILTIN AGDATCM       TC       #-}
  {-# BUILTIN AGDATCMRETURN returnTC #-}
  {-# BUILTIN AGDATCMBIND   bindTC   #-}


The ``TC`` monad provides an interface to the Agda type checker using the
following primitive operations::

  postulate
    -- Unify two terms, potentially solving metavariables in the process.
    unify : Term → Term → TC ⊤

    -- Throw a type error. Can be caught by catchTC.
    typeError : ∀ {a} {A : Set a} → List ErrorPart → TC A

    -- Block a type checking computation on a blocker. This will abort
    -- the computation and restart it (from the beginning) when the
    -- blocker has been solved.
    blockTC : ∀ {a} {A : Set a} → Blocker → TC A

    -- Prevent current solutions of metavariables from being rolled back in
    -- case 'blockOnMeta' is called.
    commitTC : TC ⊤

    -- Backtrack and try the second argument if the first argument throws a
    -- type error.
    catchTC : ∀ {a} {A : Set a} → TC A → TC A → TC A

    -- Infer the type of a given term
    inferType : Term → TC Type

    -- Check a term against a given type. This may resolve implicit arguments
    -- in the term, so a new refined term is returned. Can be used to create
    -- new metavariables: newMeta t = checkType unknown t
    checkType : Term → Type → TC Term

    -- Compute the normal form of a term.
    normalise : Term → TC Term

    -- Compute the weak head normal form of a term.
    reduce : Term → TC Term

    -- Get the current context. Returns the context in reverse order, so that
    -- it is indexable by deBruijn index. Note that the types in the context are
    -- valid in the rest of the context. To use in the current context they need
    -- to be weakened by 1 + their position in the list.
    getContext : TC Telescope

    -- Extend the current context with a variable of the given type and its name.
    extendContext : ∀ {a} {A : Set a} → String → Arg Type → TC A → TC A

    -- Set the current context relative to the context the TC computation
    -- is invoked from.  Takes a context telescope entries in reverse
    -- order, as given by `getContext`. Each type should be valid in the
    -- context formed by the remaining elements in the list.
    inContext : ∀ {a} {A : Set a} → Telescope → TC A → TC A

    -- Quote a value, returning the corresponding Term.
    quoteTC : ∀ {a} {A : Set a} → A → TC Term

    -- Unquote a Term, returning the corresponding value.
    unquoteTC : ∀ {a} {A : Set a} → Term → TC A

    -- Quote a value in Setω, returning the corresponding Term
    quoteωTC : ∀ {A : Setω} → A → TC Term

    -- Create a fresh name.
    freshName : String → TC Name

    -- Declare a new function of the given type. The function must be defined
    -- later using 'defineFun'. Takes an Arg Name to allow declaring instances
    -- and irrelevant functions. The Visibility of the Arg must not be hidden.
    declareDef : Arg Name → Type → TC ⊤

    -- Declare a new postulate of the given type. The Visibility of the Arg
    -- must not be hidden. It fails when executed from command-line with --safe
    -- option.
    declarePostulate : Arg Name → Type → TC ⊤

    -- Declare a new datatype. The second argument is the number of parameters.
    -- The third argument is the type of the datatype, i.e. its parameters and
    -- indices. The datatype must be defined later using 'defineData'.
    declareData      : Name → Nat → Type → TC ⊤

    -- Define a declared datatype. The datatype must have been declared using
    -- 'declareData`. The second argument is a list of pairs in which each pair
    -- is the name of a constructor and its type.
    defineData       : Name → List (Σ Name (λ _ → Type)) → TC ⊤

    -- Define a declared function. The function may have been declared using
    -- 'declareDef' or with an explicit type signature in the program.
    defineFun : Name → List Clause → TC ⊤

    -- Get the type of a defined name relative to the current
    -- module. Replaces 'primNameType'.
    getType : Name → TC Type

    -- Get the definition of a defined name relative to the current
    -- module. Replaces 'primNameDefinition'.
    getDefinition : Name → TC Definition

    -- Check if a name refers to a macro
    isMacro : Name → TC Bool

    -- Generate FOREIGN pragma with specified backend and top-level backend-dependent text.
    pragmaForeign : String → String → TC ⊤

    -- Generate COMPILE pragma with specified backend, associated name and backend-dependent text.
    pragmaCompile : String → Name → String → TC ⊤

    -- Change the behaviour of inferType, checkType, quoteTC, getContext
    -- to normalise (or not) their results. The default behaviour is no
    -- normalisation.
    withNormalisation : ∀ {a} {A : Set a} → Bool → TC A → TC A
    askNormalisation  : TC Bool

    -- If 'true', makes the following primitives to reconstruct hidden arguments:
    -- getDefinition, normalise, reduce, inferType, checkType and getContext
    withReconstructed : ∀ {a} {A : Set a} → Bool → TC A → TC A
    askReconstructed  : TC Bool

    -- Whether implicit arguments at the end should be turned into metavariables
    withExpandLast : ∀ {a} {A : Set a} → Bool → TC A → TC A
    askExpandLast  : TC Bool

    -- White/blacklist specific definitions for reduction while executing the TC computation
    -- 'true' for whitelist, 'false' for blacklist
    withReduceDefs : ∀ {a} {A : Set a} → (Σ Bool λ _ → List Name) → TC A → TC A
    askReduceDefs  : TC (Σ Bool λ _ → List Name)

    -- Prints the third argument to the debug buffer in Emacs
    -- if the verbosity level (set by the -v flag to Agda)
    -- is higher than the second argument. Note that Level 0 and 1 are printed
    -- to the info buffer instead. For instance, giving -v a.b.c:10 enables
    -- printing from debugPrint "a.b.c.d" 10 msg.
    debugPrint : String → Nat → List ErrorPart → TC ⊤

    -- Return the formatted string of the argument using the internal pretty printer.
    formatErrorParts : List ErrorPart → TC String

    -- Fail if the given computation gives rise to new, unsolved
    -- "blocking" constraints.
    noConstraints : ∀ {a} {A : Set a} → TC A → TC A

    -- Run the given TC action and return the first component. Resets to
    -- the old TC state if the second component is 'false', or keep the
    -- new TC state if it is 'true'.
    runSpeculative : ∀ {a} {A : Set a} → TC (Σ A λ _ → Bool) → TC A

    -- Get a list of all possible instance candidates for the given meta
    -- variable (it does not have to be an instance meta).
    getInstances : Meta → TC (List Term)

  {-# BUILTIN AGDATCMUNIFY                      unify                      #-}
  {-# BUILTIN AGDATCMTYPEERROR                  typeError                  #-}
  {-# BUILTIN AGDATCMBLOCK                      blockTC                    #-}
  {-# BUILTIN AGDATCMCATCHERROR                 catchTC                    #-}
  {-# BUILTIN AGDATCMINFERTYPE                  inferType                  #-}
  {-# BUILTIN AGDATCMCHECKTYPE                  checkType                  #-}
  {-# BUILTIN AGDATCMNORMALISE                  normalise                  #-}
  {-# BUILTIN AGDATCMREDUCE                     reduce                     #-}
  {-# BUILTIN AGDATCMGETCONTEXT                 getContext                 #-}
  {-# BUILTIN AGDATCMEXTENDCONTEXT              extendContext              #-}
  {-# BUILTIN AGDATCMINCONTEXT                  inContext                  #-}
  {-# BUILTIN AGDATCMQUOTETERM                  quoteTC                    #-}
  {-# BUILTIN AGDATCMUNQUOTETERM                unquoteTC                  #-}
  {-# BUILTIN AGDATCMQUOTEOMEGATERM             quoteωTC                   #-}
  {-# BUILTIN AGDATCMFRESHNAME                  freshName                  #-}
  {-# BUILTIN AGDATCMDECLAREDEF                 declareDef                 #-}
  {-# BUILTIN AGDATCMDECLAREPOSTULATE           declarePostulate           #-}
  {-# BUILTIN AGDATCMDECLAREDATA                declareData                #-}
  {-# BUILTIN AGDATCMDEFINEDATA                 defineData                 #-}
  {-# BUILTIN AGDATCMDEFINEFUN                  defineFun                  #-}
  {-# BUILTIN AGDATCMGETTYPE                    getType                    #-}
  {-# BUILTIN AGDATCMGETDEFINITION              getDefinition              #-}
  {-# BUILTIN AGDATCMCOMMIT                     commitTC                   #-}
  {-# BUILTIN AGDATCMISMACRO                    isMacro                    #-}
  {-# BUILTIN AGDATCMWITHNORMALISATION          withNormalisation          #-}
  {-# BUILTIN AGDATCMWITHRECONSTRUCTED          withReconstructed          #-}
  {-# BUILTIN AGDATCMWITHEXPANDLAST             withExpandLast             #-}
  {-# BUILTIN AGDATCMWITHREDUCEDEFS             withReduceDefs             #-}
  {-# BUILTIN AGDATCMASKNORMALISATION           askNormalisation           #-}
  {-# BUILTIN AGDATCMASKRECONSTRUCTED           askReconstructed           #-}
  {-# BUILTIN AGDATCMASKEXPANDLAST              askExpandLast              #-}
  {-# BUILTIN AGDATCMASKREDUCEDEFS              askReduceDefs              #-}
  {-# BUILTIN AGDATCMDEBUGPRINT                 debugPrint                 #-}
  {-# BUILTIN AGDATCMNOCONSTRAINTS              noConstraints              #-}
  {-# BUILTIN AGDATCMRUNSPECULATIVE             runSpeculative             #-}
  {-# BUILTIN AGDATCMGETINSTANCES               getInstances               #-}

Metaprogramming
---------------

There are three ways to run a metaprogram (``TC`` computation). To run
a metaprogram in a term position you use a :ref:`macro <macros>`. To
run metaprograms to create top-level definitions you can use the
``unquoteDecl`` and ``unquoteDef`` primitives (see `Unquoting
Declarations`_).

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
``f : Term → Name → Bool → Term → TC ⊤`` desugars into:

.. code-block:: agda

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

Reflected macro calls are constructed using the ``def`` constructor, so given a
macro ``g : Term → TC ⊤`` the term ``def (quote g) []`` unquotes to a macro
call to ``g``.

.. note::
   The ``quoteTerm`` and ``unquote`` primitives are available in the language,
   but it is recommended to avoid using them in favour of macros.

Limitations:

  - Macros cannot be recursive. This can be worked around by defining the
    recursive function outside the macro block and have the macro call the
    recursive function.

Silly example:

..
  ::
  module example₁ where

::

    macro
        plus-to-times : Term → Term → TC ⊤
        plus-to-times (def (quote _+_) (a ∷ b ∷ [])) hole =
          unify hole (def (quote _*_) (a ∷ b ∷ []))
        plus-to-times v hole = unify hole v

    thm : (a b : Nat) → plus-to-times (a + b) ≡ a * b
    thm a b = refl

Macros lets you write tactics that can be applied without any syntactic
overhead. For instance, suppose you have a solver::

  magic : Type → Term

..
  ::
  postulate God : (A : Set) → A
  magic t =
    def (quote God)
        (arg (arg-info visible (modality relevant quantity-ω)) t ∷ [])

that takes a reflected goal and outputs a proof (when successful). You can then
define the following macro::

  macro
    by-magic : Term → TC ⊤
    by-magic hole =
      bindTC (inferType hole) λ goal →
      unify hole (magic goal)

This lets you apply the magic tactic as a normal function:

..
  ::

  module P≠NP where
    postulate T : Set
    postulate P NP : T

::

    thm : ¬ P ≡ NP
    thm = by-magic

.. _unquoting-declarations:

Tactic Arguments
~~~~~~~~~~~~~~~~

You can declare tactics to be used to solve a particular implicit argument
using a ``@(tactic t)`` annotation. The provided tactic should be a term
``t : Term → TC ⊤``. For instance,

::

  defaultTo : {A : Set} (x : A) → Term → TC ⊤
  defaultTo x hole = bindTC (quoteTC x) (unify hole)

  f : {@(tactic defaultTo true) x : Bool} → Bool
  f {x} = x

  test-f : f ≡ true
  test-f = refl

At calls to `f`, `defaultTo true` is called on the
metavariable inserted for `x` if it is not given explicitly.
The tactic can depend on previous arguments to the function.
For instance,

::

  g : (x : Nat) {@(tactic defaultTo x) y : Nat} → Nat
  g x {y} = x + y

  test-g : g 4 ≡ 8
  test-g = refl

Record fields can also be annotated with a tactic, allowing them to be
omitted in constructor applications, record constructions and co-pattern
matches::

  record Bools : Set where
    constructor mkBools
    field fst : Bool
          @(tactic defaultTo fst) {snd} : Bool
  open Bools

  tt₀ tt₁ tt₂ tt₃ : Bools
  tt₀ = mkBools true {true}
  tt₁ = mkBools true
  tt₂ = record{ fst = true }
  tt₃ .fst = true

  test-tt : tt₁ ∷ tt₂ ∷ tt₃ ∷ [] ≡ tt₀ ∷ tt₀ ∷ tt₀ ∷ []
  test-tt = refl

Unquoting Declarations
~~~~~~~~~~~~~~~~~~~~~~

While macros let you write metaprograms to create terms, it is also useful to
be able to create top-level definitions. You can do this from a macro using the
``declareDef``, ``declareData``, ``defineFun`` and ``defineData`` primitives,
but there is no way to bring such definitions into scope. For this purpose
there are two top-level primitives ``unquoteDecl`` and ``unquoteDef`` that runs
a ``TC`` computation in a declaration position. They both have the same form
for declaring function definitions:

.. code-block:: agda

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

One advantage of ``unquoteDef`` over ``unquoteDecl`` is that
``unquoteDef`` is allowed in mutual blocks, allowing mutually
recursion between generated definitions and hand-written definitions.

Example usage:

..
  ::

  module unquote-id where

    _>>=_ = bindTC
    _>>_ : ∀ {ℓ} {A : Set ℓ} → TC ⊤ → TC A → TC A
    a >> b = a >>= λ { tt → b }

::

    arg′ : {A : Set} → Visibility → A → Arg A
    arg′ v = arg (arg-info v (modality relevant quantity-ω))

    -- Defining: id-name {A} x = x
    defId : (id-name : Name) → TC ⊤
    defId id-name = do
      defineFun id-name
        [ clause
          ( ("A" , arg′ visible (agda-sort (lit 0)))
          ∷ ("x" , arg′ visible (var 0 []))
          ∷ [])
          ( arg′ hidden (var 1)
          ∷ arg′ visible (var 0)
          ∷ [] )
          (var 0 [])
        ]

    id : {A : Set} (x : A) → A
    unquoteDef id = defId id

    mkId : (id-name : Name) → TC ⊤
    mkId id-name = do
      ty ← quoteTC ({A : Set} (x : A) → A)
      declareDef (arg′ visible id-name) ty
      defId id-name

    unquoteDecl id′ = mkId id′

Another form of ``unquoteDecl`` is used to declare data types:

.. code-block:: agda

  unquoteDecl data x constructor c₁ .. cₙ = m

``m`` is a metaprogram required to declare and define a data type ``x`` and
its constructors ``c₁`` to ``cₙ`` using ``declareData`` and ``defineData``.

System Calls
~~~~~~~~~~~~

It is possible to run system calls as part of a metaprogram, using the ``execTC`` builtin.
You can use this feature to implement type providers, or to call external solvers.
For instance, the following example calls ``/bin/echo`` from Agda:

.. code-block:: agda

  postulate
    execTC : (exe : String) (args : List String) (stdIn : String)
           → TC (Σ Nat (λ _ → Σ String (λ _ → String)))

  {-# BUILTIN AGDATCMEXEC execTC #-}

  macro
    echo : List String → Term → TC ⊤
    echo args hole = do
      (exitCode , (stdOut , stdErr)) ← execTC "echo" args ""
      unify hole (lit (string stdOut))

  _ : echo ("hello" ∷ "world" ∷ []) ≡ "hello world\n"
  _ = refl

The ``execTC`` builtin takes three arguments:
the basename of the executable (e.g., ``"echo"``),
a list of arguments,
and the contents of the standard input.
It returns a triple, consisting of
the exit code (as a natural number),
the contents of the standard output,
and the contents of the standard error.

It would be ill-advised to allow Agda to make arbitrary system calls.
Hence, the feature must be activated by passing the :option:`--allow-exec` option,
either on the command-line or using a pragma.
(Note that :option:`--allow-exec` is incompatible with :option:`--safe`.)
Furthermore, Agda can only call executables which are listed in the list of
trusted executables, ``~/.agda/executables``.
For instance, to run the example above, you must add ``/bin/echo`` to this file:

.. code-block:: text

  # contents of ~/.agda/executables
  /bin/echo

The executable can then be called by passing its basename to ``execTC``,
subtracting the ``.exe`` on Windows.
