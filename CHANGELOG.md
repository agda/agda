Release notes for Agda version 2.6.2
====================================

Highlights
----------

* Several improvements and bug-fixes related to [Run-time
  Irrelevance](https://agda.readthedocs.io/en/v2.6.2/language/runtime-irrelevance.html).

* Several improvements and bug-fixes related to the [JavaScript
  Backend](https://agda.readthedocs.io/en/v2.6.2/tools/compilers.html#javascript-backend).

* Added experimental support for [Guarded Cubical
  Agda](https://agda.readthedocs.io/en/v2.6.2/language/guarded-cubical.html).

* The [Primitive
  Sorts](https://agda.readthedocs.io/en/v2.6.2/language/built-ins.html#sorts)
  of Agda (`Set` and `Prop`) are no longer keywords and can be renamed
  when importing `Agda.Primitive`.

* Added native support for the [Inspect
  Idiom](https://agda.readthedocs.io/en/v2.6.2/language/with-abstraction.html#with-abstraction-equality).

* Added support for making [System
  Calls](https://agda.readthedocs.io/en/v2.6.2/language/reflection.html#system-calls)
  from the reflection API.

Installation and infrastructure
-------------------------------

* Added support for GHC 8.10.5 and 9.0.1.

* Some expensive optimisations are now off by default
  (see [#4521](https://github.com/agda/agda/issues/4521)).

  These optimisations can in some cases make Agda substantially
  faster, but they can also make the compilation of the Agda program
  take more time and space.

  The optimisations can be turned on manually (Cabal:
  `-foptimise-heavily`, Stack: `--flag Agda:optimise-heavily`). They
  are turned on (by default) when Agda is installed using `make
  install`.

  If the optimisations are turned on it might make sense to limit
  GHC's memory usage (using something like `--ghc-options="+RTS -M6G
  -RTS"`).

Pragmas and options
-------------------

* New option `--auto-inline` turns on automatic compile-time inlining
  of simple functions. This was previously enabled by default.

  Note that the absence of automatic inlining can make typechecking
  substantially slower.

  The new default has repercussions on termination checking, for instance
  (see [#4702](https://github.com/agda/agda/issues/4702)).
  The following formulation of `plus` termination checks with `--auto-inline`
  but not without:
  ```agda
  open import Agda.Builtin.Nat

  case_of_ : {A B : Set} → A → (A → B) → B
  case x of f = f x

  plus : Nat → Nat → Nat
  plus m n = case m of λ
     { zero    → n
     ; (suc m) → suc (plus m n)
     }
  ```
  In this particular case, we can work around the limitation of the
  termination checker with pragma `{-# INLINE case_of_ #-}`.

* New options `--qualified-instances` (default) and
  `--no-qualified-instances`. When `--no-qualified-instances` is
  enabled, Agda will only consider candidates for instance search that
  are in scope under an unqualified name (see
  [#4522](https://github.com/agda/agda/pull/4522)).

* New option `--call-by-name` turns off call-by-need evaluation at type
  checking time.

* New option `--highlight-occurrences` (off by default) enables the HTML
  backend to include a JavaScript file that highlights all occurrences of
  the mouse-hovered symbol (see
  [#4535](https://github.com/agda/agda/pull/4535)).

* New option `--no-import-sorts` disables the implicit `open
  import Agda.Primitive using (Set; Prop)` at the top of each file
  (see below).

* New option `--local-confluence-check` to restore the old behaviour
  of the `--confluence-check` flag (see below for the new behaviour).

* New primitive `primStringFromListInjective` internalising the fact that
  `primStringFromList` is an injective function. It is bound in
  `Agda.Builtin.String.Properties`.

* New option `--allow-exec` enables the use of system calls during
  type checking using the `AGDATCMEXECTC` builtin.

* New option `--show-identity-substitutions` shows all arguments of
  metavariables when pretty-printing a term, even if they amount to
  just applying all the variables in the context.

* The option `--rewriting` is now considered infective: if a module has
  `--rewriting` enabled, then all modules importing it must also have
  `--rewriting` enabled.

* New option `--no-double-check` (default), opposite of the existing
  `--double-check`.

* Due to several known soundness issues with sized types (see
  [#1201](https://github.com/agda/agda/issues/1201),
  [#1946](https://github.com/agda/agda/issues/1946),
  [#2820](https://github.com/agda/agda/issues/2820),
  [#3026](https://github.com/agda/agda/issues/3026)), the
  `--sized-types` flag can no longer be used while `--safe` is active.

* New option `--guarded` turns on the Guarded Cubical extension of Agda.

  See [Guarded Cubical](https://agda.readthedocs.io/en/v2.6.2/language/guarded-cubical.html)
  in the documentation for more.

* The flags `--guardedness` and `--sized-types` are no longer enabled
  by default.

Command-line interaction
------------------------

* In the previous release, Agda exited with either status 0 when the
  program type checks successfully, or status 1 when encountering any
  kind of error.  Now Agda exits with status 42 for type errors, 71
  for errors in the commandline arguments, and 154 for impossible
  errors. Exit status 1 may be returned under other circumstances; for
  instance, an incomplete pattern matching, or an error generated by
  the Haskell runtime.  See PR
  [#4540](https://github.com/agda/agda/pull/4540).

Lexical syntax
--------------

* Layout handling has been improved so that block starters can be
  stacked on the same line
  [#1145](https://github.com/agda/agda/issues/1145).

  If several layout blocks are started by layout keywords without line
  break in between (where line breaks inside block comments do not
  count), then those blocks indented *more* than the last block go
  passive, meaning they cannot be further extended by new statements.
  ```agda
    private module M where postulate
              A : Set                 -- module-block goes passive
              B : Set                 -- postulate-block can still be extended
            module N where            -- private-block can still be extended
  ```
  Previously, this was a parse error.

Language
--------

* Inductive records without η-equality no longer support both matching
  on the record constructor and construction of record elements by
  copattern matching.  It has been discovered that the combination of
  both leads to loss of subject reduction, i.e., reduction does not
  preserve typing.  See issue
  [#4560](https://github.com/agda/agda/issues/4560).

  η-equality for a record can be turned off manually with directive
  `no-eta-equality` or command-line option `--no-eta-equality`, but it
  is also automatically turned off for some recursive records.  For
  records without η, matching on the record constructor is now off by
  default and construction by copattern matching is on.  If you want
  the converse, you can add the new record directive `pattern`.

  Example with record pattern:
  ```agda
  record N : Set where
    inductive
    no-eta-equality
    pattern
    field out : Maybe N

  pred : N → Maybe N
  pred record{ out = m } = m
  ```
  Example with record constructor and use of `;` instead of newline:
  ```agda
  record N : Set where
    inductive; no-eta-equality
    pattern; constructor inn
    field out : Maybe N

  pred : N → Maybe N
  pred (inn m) = m
  ```

* `Set` and `Prop` are no longer keywords but are now primitives
  defined in the module `Agda.Primitive`. They can be renamed when
  importing this module, for example:

  ```agda
  open import Agda.Primitive renaming (Set to Type)

  test : Type₁
  test = Type
  ```

  To preserve backwards compatibility, each top-level Agda module now
  starts with an implicit statement:

  ```agda
  open import Agda.Primitive using (Set; Prop)
  ```

  This implicit import can be disabled with the
  `--no-import-sorts` flag.

* Agda now has support for sorts `Setωᵢ` (alternative syntax: `Setωi`)
  for natural numbers `i`, where `Setω₀ = Setω`. These sorts form a
  second hierarchy `Setωᵢ : Setωᵢ₊₁` similar to the standard hierarchy
  of `Setᵢ`, but do not support universe polymorphism. It should not
  be necessary to refer to these sorts during normal usage of Agda,
  but they might be useful for defining reflection-based macros (see
  [#2119](https://github.com/agda/agda/issues/2119) and
  [#4585](https://github.com/agda/agda/issues/4585)).

* Changed the internal representation of literal strings: instead of using a
  linked list of characters (`String`), we are now using `Data.Text`. This
  should be a transparent change from the user's point of view: the backend
  was already packing these strings as text.

  Used this opportunity to introduce a `primStringUncons` primitive in
  `Agda.Builtin.String` (and to correspondingly add the
  `Agda.Builtin.Maybe` it needs).

* The option `--confluence-check` for rewrite rules has been given a
  new implementation that checks global confluence instead of local
  confluence. Concretely, it does so by enforcing two properties:

  1. For any two left-hand sides of the rewrite rules that overlap
     (either at the root position or at a subterm), the most general
     unifier of the two left-hand sides is again a left-hand side of a
     rewrite rule. For example, if there are two rules `suc m + n =
     suc (m + n)` and `m + suc n = suc (m + n)`, then there should
     also be a rule `suc m + suc n = suc (suc (m + n))`.

  2. Each rewrite rule should satisfy the *triangle property*: For any
     rewrite rule `u = w` and any single-step parallel unfolding `u =>
     v`, we should have another single-step parallel unfolding `v =>
     w`.

  The previous behaviour of the confluence checker that only ensures
  local confluence can be restored by using the
  `--local-confluence-check` flag.

* Binary integer literals with prefix `0b` (for instance,
  `0b11001001`) are now supported.

* Overloaded literals now require the conversion function (`fromNat`,
  `fromNeg`, or `fromString`) to be in scope *unqualified* to take
  effect.

  Previously, it was enough for the function to be in scope at all,
  which meant you couldn't import the corresponding builtin module
  without having overloaded literals turned on.

* Added `interleaved mutual` blocks where users can forward-declare
  function, record, and data types and interleave their
  definitions. These blocks are elaborated to more traditional mutual
  blocks by:

    - leaving the signatures where they are
    - grouping the clauses for a function together with the first of them
    - grouping the constructors for a datatype together with the first of them

  Example: two interleaved function definitions

  ```agda

  interleaved mutual

    -- Declarations:
    even : Nat → Bool
    odd  : Nat → Bool

    -- zero is even, not odd
    even zero = true
    odd  zero = false

    -- suc case: switch evenness on the predecessor
    even (suc n) = odd n
    odd  (suc n) = even n
  ```

  Other example: the definition of universe of types closed under the
  natural numbers and pairing:

  ```agda

  interleaved mutual

    -- Declaration of a product record, a universe of codes, and a decoding function
    record _×_ (A B : Set) : Set
    data U : Set
    El : U → Set

    -- We have a code for the type of natural numbers in our universe
    constructor `Nat : U
    El `Nat = Nat

    -- Btw we know how to pair values in a record
    record _×_ A B where
      constructor _,_
      inductive
      field fst : A; snd : B

    -- And we have a code for pairs in our universe
    constructor _`×_ : (A B : U) → U
    El (A `× B) = El A × El B
  ```

* Erased constructors (see
  [#4638](https://github.com/agda/agda/issues/4638)).

  Constructors can be marked as erased. Example:
  ```agda
    {-# OPTIONS --cubical --safe #-}

    open import Agda.Builtin.Cubical.Path
    open import Agda.Primitive

    private
      variable
        a   : Level
        A B : Set a

    Is-proposition : Set a → Set a
    Is-proposition A = (x y : A) → x ≡ y

    data ∥_∥ (A : Set a) : Set a where
      ∣_∣        : A → ∥ A ∥
      @0 trivial : Is-proposition ∥ A ∥

    rec : @0 Is-proposition B → (A → B) → ∥ A ∥ → B
    rec p f ∣ x ∣           = f x
    rec p f (trivial x y i) = p (rec p f x) (rec p f y) i
  ```
  In the code above the constructor `trivial` is only available at
  compile-time, whereas `∣_∣` is also available at run-time. Erased
  names can be used in bodies of clauses that match on `trivial`, if
  the match is done in a non-erased position, like in the final clause
  of `rec`. (Note that Cubical Agda programs still cannot be
  compiled.)

* Erased pattern-matching lambdas (see
  [#4525](https://github.com/agda/agda/issues/4525)).

  Regular pattern-matching lambdas are treated as non-erased
  function definitions. One can make a pattern-matching lambda erased
  by writing `@0` or `@erased` after the lambda:
  ```agda
  @0 _ : @0 Set → Set
  _ = λ @0 { A → A }

  @0 _ : @0 Set → Set
  _ = λ @erased where
    A → A
  ```

  The reflection machinery currently does not support erased
  pattern-matching lambdas (they are quoted as regular
  pattern-matching lambdas).

* New (?) rule for modalities of generalised variables
  (see [#5058](https://github.com/agda/agda/issues/5058)).

  The new rule is that generalisable variables get the modality that
  they are declared with, whereas other variables always get the
  default modality. (It is unclear what the old rule was, perhaps
  nothing was changed.)

* Private abstract type signatures can no longer see through abstract
  (see [#418](https://github.com/agda/agda/issues/418)).

  This means that abstract definitions no longer evaluate in *any*
  type signatures in the same module. Previously they evaluated in
  type signatures of definitions that were both private and abstract.

  It also means that metavariables in type signatures have to be
  solved locally, and cannot make use of information in the definition
  body, and that constructors of abstract datatypes are not in scope
  in type signatures.

* Type inference is disabled for abstract definitions (see
  [#418](https://github.com/agda/agda/issues/418)).

  This means that abstract definitions (inluding functions defined in
  `where` blocks of abstract definitions) need complete type
  signatures.

* One can now declare syntax with two name parts without any hole in
  between, and syntax without any holes.

  Examples:
  ```agda
  syntax Σ A (λ x → B) = [ x ∶ A ] × B
  syntax []            = [ ]
  ```

* Internalised the *inspect idiom* that allows users to abstract over
  an expression in a ``with`` clause while, at the same time,
  remembering the origin of the abstracted pattern via an equation.

  In the following example, abstracting over and then matching on the
  result of ``p x`` allows the first call to ``filter p (x ∷ xs)`` to
  reduce.

  In case the element ``x`` is kept, the second call to ``filter`` on
  the LHS then performs the same ``p x`` test. Because we have
  retained the proof that ``p x ≡ true`` in ``eq``, we are able to
  rewrite by this equality and get it to reduce too.

  This leads to just enough computation that we can finish the proof
  with an appeal to congruence and the induction hypothesis.

  ```agda
  filter-filter : ∀ p xs → filter p (filter p xs) ≡ filter p xs
  filter-filter p []       = refl
  filter-filter p (x ∷ xs) with p x in eq
  ... | false = filter-filter p xs -- easy
  ... | true -- second filter stuck on `p x`: rewrite by `eq`!
    rewrite eq = cong (x ∷_) (filter-filter p xs)
  ```

* As a consequence of the above extensions to `with`, lambdas and lets
  now need parentheses when appearing in a `with`. For instance,

  ```agda
  with-on-fun : Nat → Nat
  with-on-fun n with (λ m → m + n)  -- parentheses required!
  ... | f = f n
  ```

* It is now possible to add hiding and relevance annotations to `with`
  expressions. For example:

  ```agda
  module _ (A B : Set) (recompute : .B → .{{A}} → B) where

    _$_ : .(A → B) → .A → B
    f $ x with .{f} | .(f x) | .{{x}}
    ... | y = recompute y
  ```

Builtins
--------

- Primitive operations for floating-point numbers changed. The equalities now
  follow IEEE 754 equality, after unifying all NaNs. Primitive inequality was
  added:
  ```agda
  primFloatEquality   : Float -> Float -> Bool -- from primFloatNumericEquality
  primFloatLess       : Float -> Float -> Bool -- from primFloatNumericLess
  primFloatInequality : Float -> Float -> Bool -- new
  ```
  The “numeric” relations are now deprecated.

  There are several new predicates on floating-point numbers:
  ```agda
  primFloatIsInfinite     : Float -> Bool -- new
  primFloatIsNaN          : Float -> Bool -- new
  primFloatIsSafeInteger  : Float -> Bool -- new
  ```
  The `primFloatIsSafeInteger` function determines whether the value is a number
  that is a safe integer, i.e., is within the range where the arithmetic
  operations do not lose precision.

  The operations for conversion to integers (`primRound`, `primFloor`,
  and `primCeiling`) were renamed for consistency, and return a value
  of type `Maybe Int`, returning `nothing` for NaN and the infinities:
  ```agda
  primFloatRound   : Float → Maybe Int -- from primRound
  primFloatFloor   : Float → Maybe Int -- from primFloor
  primFloatCeiling : Float → Maybe Int -- from primCeiling
  ```

  There are several new conversions:
  ```agda
  primIntToFloat    : Int -> Float               -- new
  primFloatToRatio  : Float -> (Int × Nat)       -- new
  primRatioToFloat  : Int -> Nat -> Float        -- new
  primFloatDecode   : Float -> Maybe (Int × Int) -- new
  primFloatEncode   : Int -> Int -> Maybe Float  -- new
  ```
  The `primFloatDecode` function decodes a floating-point number f to a mantissa
  and exponent, such that `f = mantissa * 2 ^ exponent`, normalised such that
  the mantissa is the smallest possible number. The `primFloatEncode` function
  encodes a pair of a mantissa and exponent to a floating-point number.

  There are several new operations:
  ```agda
  primFloatPow        : Float -> Float -> Float -- new
  primFloatATan2      : Float -> Float -> Float -- from primATan2
  primFloatSinh       : Float -> Float          -- new
  primFloatCosh       : Float -> Float          -- new
  primFloatTanh       : Float -> Float          -- new
  primFloatASinh      : Float -> Float          -- new
  primFloatACosh      : Float -> Float          -- new
  primFloatATanh      : Float -> Float          -- new
  ```
  Furthermore, the following operations were renamed for consistency:
  ```agda
  primFloatExp        : Float -> Float          -- from primExp
  primFloatSin        : Float -> Float          -- from primSin
  primFloatLog        : Float -> Float          -- from primLog
  primFloatCos        : Float -> Float          -- from primCos
  primFloatTan        : Float -> Float          -- from primTan
  primFloatASin       : Float -> Float          -- from primASin
  primFloatACos       : Float -> Float          -- from primACos
  primFloatATan       : Float -> Float          -- from primATan
  ```

  All of these operations are implemented on the JavaScript backend.

- `primNatToChar` maps surrogate code points to the replacement character
  `'U+FFFD` and surrogate code points are disallowed in character literals

  [Surrogate code points](https://www.unicode.org/glossary/#surrogate_code_point)
  are characters in the range `U+D800` to `U+DFFF` and are reserved for use by
  UTF-16.

  The reason for this change is that strings are represented (at type-checking
  time and in the GHC backend) by Data.Text byte strings, which cannot
  represent surrogate code points and replaces them by `U+FFFD`. By doing the
  same for characters we can have `primStringFromList` be injective (witnessed
  by `Agda.Builtin.String.Properties.primStringFromListInjective`).


Reflection
----------

- New operation in `TC` monad, similar to `quoteTC` but operating on
  types in `Setω`
  ```agda
  quoteωTC : ∀ {A : Setω} → A → TC Term
  ```
- `typeError` and `debugPrint` no longer inserts spaces around `termErr` and
  `nameErr` parts. They also do a better job of respecting line breaks in
  `strErr` parts.

- The reflection machinery now supports quantities in `Arg` (see
  [#5317](https://github.com/agda/agda/issues/5317)). The `ArgInfo`
  type has changed, and there are new types `Modality` and `Quantity`:
  ```agda
  data Quantity : Set where
    quantity-0 quantity-ω : Quantity

  {-# BUILTIN QUANTITY   Quantity   #-}
  {-# BUILTIN QUANTITY-0 quantity-0 #-}
  {-# BUILTIN QUANTITY-ω quantity-ω #-}

  data Modality : Set where
    modality : (r : Relevance) (q : Quantity) → Modality

  {-# BUILTIN MODALITY             Modality #-}
  {-# BUILTIN MODALITY-CONSTRUCTOR modality #-}

  data ArgInfo : Set where
    arg-info : (v : Visibility) (m : Modality) → ArgInfo
  ```

- The representation of reflected patterns and clauses has
  changed. Each clause now includes a telescope with the names and
  types of the pattern variables.

  ```agda
  data Clause where
    clause        : (tel : List (Σ String λ _ → Arg Type)) (ps : List (Arg Pattern)) (t : Term) → Clause
    absurd-clause : (tel : List (Σ String λ _ → Arg Type)) (ps : List (Arg Pattern)) → Clause
  ```

  These telescopes provide additional information on the types of
  pattern variables that was previously hard to reconstruct (see
  [#2151](https://github.com/agda/agda/issues/2151)). When unquoting a
  clause, the types in the clause telescope are currently ignored (but
  this is subject to change in the future).

  Three constructors of the `Pattern` datatype were also changed:

  * pattern variables now refer to a de Bruijn index (relative to the
    clause telescope) rather than a string,
  * absurd patterns take a de Bruijn index and are expected to be bound by the
    clause telescope,
  * dot patterns now include the actual dotted term.

  ```agda
  data Pattern where
    con    : (c : Name) (ps : List (Arg Pattern)) → Pattern
    dot    : (t : Term)    → Pattern   -- previously:   dot : Pattern
    var    : (x : Nat)     → Pattern   -- previously:   var : (x : String) → Pattern
    lit    : (l : Literal) → Pattern
    proj   : (f : Name)    → Pattern
    absurd : (x : Nat)     → Pattern
  ```

  It is likely that this change to the reflected syntax requires you
  to update reflection code written for previous versions of
  Agda. Here are some tips for updating your code:

  * When quoting a clause, you can recover the name of a pattern
    variable by looking up the given index in the clause
    telescope. The contents of dot patterns can safely be ignored
    (unless you have a use for them).

  * When creating a new clause for unquoting, you need to create a
    telescope for the types of the pattern variables. To get back the
    old behaviour of Agda, it is sufficient to set all the types of
    the pattern variables to `unknown`. So you can construct the
    telescope by listing the names of all pattern variables and absurd
    patterns together with their `ArgInfo`. Meanwhile, the pattern
    variables should be numbered in order to update them to the new
    representation. As for the telescope types, the contents of a
    `dot` pattern can safely be set to `unknown`.

- New operation in `TC` monad, `execTC`, which calls an external executable
  ```agda
  execTC : (exe : String) (args : List String) (stdIn : String)
         → TC (Σ Nat (λ _ → Σ String (λ _ → String)))
  ```
  The `execTC` builtin takes three arguments: the basename of the
  executable (e.g., `"echo"`), a list of arguments, and the contents
  of the standard input. It returns a triple, consisting of the exit
  code (as a natural number), the contents of the standard output, and
  the contents of the standard error.

  The builtin is only available when `--allow-exec` is passed. (Note
  that `--allow-exec` is incompatible with ``--safe``.) To make an
  executable available to Agda, add the absolute path on a new line in
  `~/.agda/executables`.

- Two new operations in the `TC` monad, `onlyReduceDefs` and
  `dontReduceDefs`:
  ```agda
  onlyReduceDefs : ∀ {a} {A : Set a} → List Name → TC A → TC A
  dontReduceDefs : ∀ {a} {A : Set a} → List Name → TC A → TC A
  ```
  These functions allow picking a specific set of functions that
  should (resp. should not) be reduced while executing the given `TC`
  computation.

  For example, the following macro unifies the current hole with the
  term `3 - 3`:
  ```agda
  macro₁ : Term -> TC ⊤
  macro₁ goal = do
    u   ← quoteTC ((1 + 2) - 3)
    u'  ← onlyReduceDefs (quote _+_ ∷ []) (normalise u)
    unify u' goal
  ```
- New operation in the `TC` monad, `withReconstructed`:
  ```agda
  withReconstructed : ∀ {a} {A : Set a} → TC A → TC A
  ```

  This function ensures reconstruction of hidden parameters
  after performing the `TC` computation.  For example, consider the
  following type and function:
  ```agda
  record RVec {a} (X : Set a) (n : Nat) : Set a where
    constructor vec
    field sel : Fin n → X

  test-rvec : Nat → RVec Nat 5
  test-rvec x = vec λ _ → x
  ```

  In the reflected syntax the body of the `test-rvec` would be represented
  as `con vec (unknown ∷ unknown ∷ unknown ∷ (lam _ x)`.  The use of
  `withReconstructed` replaces `unknown`s with the actual values:
  ```agda
  macro₂ : Name → Term → TC ⊤
  macro₂ n hole = do
    (function (clause tel ps t ∷ [])) ←
      withReconstructed (getDefinition n)
      where _ → quoteTC "ERROR" >>= unify hole
    quoteTC t >>= unify hole
  ```

- Three new constructors in the `Sort` datatype, `prop : Level →
  Sort`, `propLit : Nat → Sort`, and `inf : Nat → Sort`, representing
  the sorts `Prop ℓ`, `Propᵢ`, and `Setωᵢ`.

- Terms that belong to a type in `Prop` are no longer unquoted to
  `unknown` but to a proper `Term`. (See
  [#3553](https://github.com/agda/agda/issues/3553).)

Library management
------------------

- `.agda-lib` files can now contain an extra field `flags:` with
  default flags for the library. Flags can be any flags that are
  accepted as part of an `{-# OPTIONS ... #-}` pragma. For example,
  file `my-library.agda-lib` with

  ```
  flags: --without-K
  ```

  will apply the `--without-K` flag to all Agda files in the current
  directory and (recursive) subdirectories that do not themselves
  contain an `.agda-lib` file.


Emacs mode
----------

* New command prefix `C-u C-u C-u` for weak-head normalization. For instance,
  given

  ```agda
  downFrom : Nat → List Nat
  downFrom 0 = []
  downFrom (suc n) = n ∷ downFrom n
  ```

  `C-u C-u C-u C-c C-n downFrom 5` returns `4 ∷ downFrom 4`.

* New keyboard shortcut `C-c C-x C-i` for toggling display of
  irrelevant arguments.

* One can no longer use commands like `M-;` (`comment-dwim`) to
  uncomment block comments. In return one can use `M-;` to comment out
  pragmas. (See [#3329](https://github.com/agda/agda/issues/3329).)

JSON Interaction mode
---------------------

Changes have been made to the structure of error and warning
messages. The changes are summarized below. See
[#5052](https://github.com/agda/agda/issues/5052) for additional
details.

* The format of an error or warning was previously a bare string. Now, errors
  and warnings are represented by an object with a `"message"` key.

  This means that responses _previously_ structured like:

  ```json
  {"…": "…", "error": "Foo bar baz"}
  ```

  will now be structured:

  ```json
  {"…": "…", "error": {"message": "Foo bar baz"}}
  ```

  This applies directly to the `PostPonedCheckFunDef` response kind
  and `Error` info kind of the `DisplayInfo` response kind.

* The format of collections of errors or warnings, which previously were each
  represented by a single newline-joined string, has been updated to represent
  each warning or error individually in a list.

  That means that responses _previously_ structured like:

  ```json
  { "…": "…"
  , "errors": "Postulates overcooked\nAxioms too wiggly"
  , "warnings": "Something wrong\nSomething else\nwrong"
  }
  ```

  will now be structured:

  ```json
  { "…": "…"
  , "errors":
    [ { "message": "Postulates overcooked" }
    , { "message": "Axioms too wiggly" }
    ]
  , "warnings":
    [ { "message": "Something wrong" }
    , { "message": "Something else\nwrong" }
    ]
  }
  ```

  This applies to `CompilationOk`, `AllGoalsWarning`, and `Error` info
  kinds of the `DisplayInfo` response kind.

* The `Error` info kind of the `DisplayInfo` response kind has
  additionally been updated to distinguish warnings and errors.

  An example of the _previous_ format of a `DisplayInfo` response with
  an `Error` info kind was:
  ```json
  {
    "kind": "DisplayInfo",
    "info": {
      "kind": "Error",
      "message": "———— Error —————————————————————————————————————————————————\n/data/code/agda-test/Test.agda:2,1-9\nFailed to find source of module M in any of the following\nlocations:\n  /data/code/agda-test/M.agda\n  /data/code/agda-test/M.lagda\nwhen scope checking the declaration\n  import M\n\n———— Warning(s) ————————————————————————————————————————————\n/data/code/agda-test/Test.agda:3,1-10\nEmpty postulate block."
    }
  }
  ```

  The updated format is:
  ```json
  {
    "kind": "DisplayInfo",
    "info": {
      "kind": "Error",
      "error": {
        "message": "/data/code/agda-test/Test.agda:2,1-9\nFailed to find source of module M in any of the following\nlocations:\n  /data/code/agda-test/M.agda\n  /data/code/agda-test/M.lagda\nwhen scope checking the declaration\n  import M"
      },
      "warnings": [
        {
          "message": "/data/code/agda-test/Test.agda:3,1-10\nEmpty postulate block."
        }
      ]
    }
  }
  ```

Compiler backends -----------------

- With option `--allow-unsolved-metas`, code with holes can be compiled.
  If a hole is reached at runtime, the compiled program crashes.
  See issue [#5103](https://github.com/agda/agda/issues/5103)

- Previously the GHC backend compiled at least one instance of Hinze's
  memoisation technique from ["Memo functions,
  polytypically!"](http://www.cs.ox.ac.uk/ralf.hinze/publications/index.html#P11)
  to reasonably efficient code. That is no longer the case (at least
  for that particular instance, see
  [#5153](https://github.com/agda/agda/issues/5153)).

LaTeX backend
-------------

- The spacing in comments is now preserved when generating LaTex files
  from literate Agda.  See
  [#5320](https://github.com/agda/agda/pull/5320) for more details.

HTML backend
------------

- The named `id` attributes for local modules inside local modules are
  now different (see [#5335](https://github.com/agda/agda/pull/5320)).

  For instance, consider the following Agda file:
  ```agda
  module Top-level where

    module Inner where

      module Inside-inner where
  ```
  Previously one could link to the module `Inside-inner` using a URL
  that ended with `#Inside-inner`. Now one can use
  `#Inner.Inside-inner` instead.

JS backend
----------

- Smaller local variable names in the generated JS code.

  Previously: `x0`, `x1`, `x2`, ...

  Now: `a`, `b`, `c`, ..., `z`, `a0`, `b0`, ..., `z0`, `a1`, `b1`, ...

- Improved indentation of generated JS code.

- More compact rendering of generated JS functions.

  Previously:
  ```js
  exports["N"]["suc"] = function (x0) {
      return function (x1) {
        return x1["suc"](x0);
      };
    };
  ```

  Now:
  ```js
  exports["N"]["suc"] = a => b => b["suc"](a);
  ```

- Irrelevant arguments are now erased in the generated JS code.

  Example Agda code:
  ```agda
  flip : {A B C : Set} -> (B -> A -> C) -> A -> B -> C
  flip f a b = f b a
  ```

  Previously generated JS code:
  ```js
  exports["flip"] = function (x0) {
      return function (x1) {
        return function (x2) {
          return function (x3) {
            return function (x4) {
              return function (x5) {
                return x3(x5)(x4);
              };
            };
          };
        };
      };
    };
  ```

  JS code generated now:
  ```js
  exports["flip"] = a => b => c => a(c)(b);
  ```

- Record fields are not stored separately (the fields are stored only
  in the constructor) in the generated JS code.

  Example Agda code:
  ```agda
  record Sigma (A : Set) (B : A -> Set) : Set where
    field
      fst : A
      snd : B fst
  ```

  Previously generated JS code (look at the `"fst"` and `"snd"` fields in the
  return value of `exports["Sigma"]["record"]`:
  ```js
  exports["Sigma"] = {};
  exports["Sigma"]["fst"] = function (x0) {
      return x0["record"]({
        "record": function (x1, x2) {
          return x1;
        }
      });
    };
  exports["Sigma"]["snd"] = function (x0) {
      return x0["record"]({
        "record": function (x1, x2) {
          return x2;
        }
      });
    };
  exports["Sigma"]["record"] = function (x0) {
      return function (x1) {
        return {
          "fst": x0,
          "record": function (x2) {
            return x2["record"](x0, x1);
          },
          "snd": x1
        };
      };
    };
  ```

  JS code generated now:
  ```js
  exports["Sigma"] = {};
  exports["Sigma"]["fst"] = a => a["record"]({"record": (b,c) => b});
  exports["Sigma"]["snd"] = a => a["record"]({"record": (b,c) => c});
  exports["Sigma"]["record"] = a => b => ({"record": c => c["record"](a,b)});
  ```

- `--js-optimize` flag has been added to the `agda` compiler.

  With `--js-optimize`, `agda` does not wrap records in JS objects.

  Example Agda code:
  ```agda
  record Sigma (A : Set) (B : A -> Set) : Set where
    field
      fst : A
      snd : B fst
  ```

  JS code generated without the `--js-optimize` flag:
  ```js
  exports["Sigma"] = {};
  exports["Sigma"]["fst"] = a => a["record"]({"record": (b,c) => b});
  exports["Sigma"]["snd"] = a => a["record"]({"record": (b,c) => c});
  exports["Sigma"]["record"] = a => b => ({"record": c => c["record"](a,b)});
  ```

  JS code generated with the `--js-optimize` flag:
  ```js
  exports["Sigma"] = {};
  exports["Sigma"]["fst"] = a => a((b,c) => b);
  exports["Sigma"]["snd"] = a => a((b,c) => c);
  exports["Sigma"]["record"] = a => b => c => c(a,b);
  ```

  With `--js-optimize`, `agda` uses JS arrays instead of JS objects.
  This is possible because constructor names are not relevant during the evaluation.

  Example Agda code:
  ```agda
  data Bool : Set where
    false : Bool
    true  : Bool

  not : Bool -> Bool
  not false = true
  not true  = false
  ```

  JS code generated without the `--js-optimize` flag:
  ```js
  exports["Bool"] = {};
  exports["Bool"]["false"] = a => a["false"]();
  exports["Bool"]["true"] = a => a["true"]();
  exports["not"] = a => a({
      "false": () => exports["Bool"]["true"],
      "true": () => exports["Bool"]["false"]
    });
  ```

  JS code generated with the `--js-optimize` flag:
  ```js
  exports["Bool"] = {};
  exports["Bool"]["false"] = a => a[0/* false */]();
  exports["Bool"]["true"] = a => a[1/* true */]();
  exports["not"] = a => a([
      /* false */() => exports["Bool"]["true"],
      /* true */() => exports["Bool"]["false"]
    ]);
  ```

  Note that comments are added to generated JS code to help human readers.

  Erased branches are replaced by `null` in the generated array.  If
  more than the half of branches are erased, the array is compressed
  to be a object like `{3: ..., 13: ...}`.

- `--js-minify` flag has been added to the `agda` compiler.

  With `--js-minify`, `agda` discards comments and whitespace in the
  generated JS code.


Agda as a library (API)
-----------------------

* The `SourceInfo` record has been renamed to `Source`, and the
  `sourceInfo` function to `parseSource`.

Other issues
------------

For 2.6.2, the following issues were also closed (see [bug
tracker](https://github.com/agda/agda/issues)):

  -  [#418](https://github.com/agda/agda/issues/418): Unifier ignores presence of abstract keyword
  -  [#958](https://github.com/agda/agda/issues/958): Module application display forms in parameterised modules
  -  [#1145](https://github.com/agda/agda/issues/1145): Allow multiple layout keywords on the same line
  -  [#2151](https://github.com/agda/agda/issues/2151): Add TC primitive to check left-hand side
  -  [#2461](https://github.com/agda/agda/issues/2461): Support with in the presence of IApply patterns
  -  [#2858](https://github.com/agda/agda/issues/2858): Feature request: Interleaving mutually-defined functions & datatypes
  -  [#3000](https://github.com/agda/agda/issues/3000): Interaction: iterated give encounters internal error
  -  [#3118](https://github.com/agda/agda/issues/3118): Feature request: default flags in .agda-lib file
  -  [#3289](https://github.com/agda/agda/issues/3289): Postfix projections should not have hiding information
  -  [#3360](https://github.com/agda/agda/issues/3360): Make Emacs mode available as a normal package via MELPA
  -  [#3365](https://github.com/agda/agda/issues/3365): Update GitHub linguist syntax highlight file
  -  [#3398](https://github.com/agda/agda/issues/3398): With the option --allow-unsolved-metas, the unsolved metas are not shown, only yellow
  -  [#3422](https://github.com/agda/agda/issues/3422): Show names of instance candidates in error message
  -  [#3486](https://github.com/agda/agda/issues/3486): Elaborate-and-give shouldn't reduce solution
  -  [#3532](https://github.com/agda/agda/issues/3532): Refine does not work for functions with 10 arguments or more
  -  [#3538](https://github.com/agda/agda/issues/3538): Regression: Rewrite rule involving constructors rejected in parametrized module
  -  [#3588](https://github.com/agda/agda/issues/3588): Refine suggests overloaded constructor which is not in scope
  -  [#3627](https://github.com/agda/agda/issues/3627): Where-blocks of clauses with irrelevant projections can use irrelevant variables
  -  [#3644](https://github.com/agda/agda/issues/3644): Error message without position
  -  [#3672](https://github.com/agda/agda/issues/3672): Better error messages for generalize easter eggs
  -  [#3684](https://github.com/agda/agda/issues/3684): Make error about non-existent record field a warning?
  -  [#3734](https://github.com/agda/agda/issues/3734): WARNING_ON_USAGE is not raised for constructors
  -  [#3744](https://github.com/agda/agda/issues/3744): Internal error related to abstract
  -  [#3870](https://github.com/agda/agda/issues/3870): Internal error during instance search
  -  [#3926](https://github.com/agda/agda/issues/3926): Document the effect of `mutual` to the order of type checking
  -  [#3933](https://github.com/agda/agda/issues/3933): `import` can remove definitions from scope
  -  [#3961](https://github.com/agda/agda/issues/3961): Missing documentation for coverage checking
  -  [#4071](https://github.com/agda/agda/issues/4071): Ill-scoped code in error message
  -  [#4088](https://github.com/agda/agda/issues/4088): Strange scoping rules for irrefutable with, part 2
  -  [#4093](https://github.com/agda/agda/issues/4093): Make it possible to rename Set?
  -  [#4109](https://github.com/agda/agda/issues/4109): cannot declare data types in Setω
  -  [#4131](https://github.com/agda/agda/issues/4131): Record definition doesn't compile without a specific `let` binding
  -  [#4132](https://github.com/agda/agda/issues/4132): The regular expression for floats in the lexer is too liberal
  -  [#4135](https://github.com/agda/agda/issues/4135): Constructor disambiguation picks non-unique solution
  -  [#4157](https://github.com/agda/agda/issues/4157): Agda gets confused by multiple anonymous definitions in a single mutual block
  -  [#4160](https://github.com/agda/agda/issues/4160): Printing implicit lambdas with --show-implicit
  -  [#4161](https://github.com/agda/agda/issues/4161): An alternative solution for hGetContent error on Windows when non-English
  -  [#4166](https://github.com/agda/agda/issues/4166): Instances that are not in scope are candidates for instance resolution
  -  [#4208](https://github.com/agda/agda/issues/4208): Field named `_` in `genTel` record
  -  [#4252](https://github.com/agda/agda/issues/4252): Interaction ids get conflated after iterated give
  -  [#4265](https://github.com/agda/agda/issues/4265): Unsolved constraints when --no-syntactic-equality is used
  -  [#4280](https://github.com/agda/agda/issues/4280): Test case for #4169 fails in JS backend
  -  [#4291](https://github.com/agda/agda/issues/4291): Incorrect names can be generated for generalised variables
  -  [#4341](https://github.com/agda/agda/issues/4341): The documentation of inContext seems wrong.
  -  [#4350](https://github.com/agda/agda/issues/4350): Scoping bug with let open in telescope
  -  [#4365](https://github.com/agda/agda/issues/4365): Module fails to type check after parametrising it by postulates
  -  [#4400](https://github.com/agda/agda/issues/4400): TERMINATING pragma in where clause
  -  [#4425](https://github.com/agda/agda/issues/4425): [doc] What are .agdai files?
  -  [#4456](https://github.com/agda/agda/issues/4456): No error highlighting for error warnings?
  -  [#4458](https://github.com/agda/agda/issues/4458): The command agda2-measure-load-time is broken
  -  [#4481](https://github.com/agda/agda/issues/4481): Named implicit arguments do not behave the same in anonymous lambdas & definitions
  -  [#4482](https://github.com/agda/agda/issues/4482): "Unexpected implicit argument" should pinpoint exactly where the error starts
  -  [#4486](https://github.com/agda/agda/issues/4486): "did you mean" hint also for failing imports
  -  [#4491](https://github.com/agda/agda/issues/4491): Add a primitive for Data.Text's uncons
  -  [#4516](https://github.com/agda/agda/issues/4516): Internal error if files cannot be written to the directory for temporary files
  -  [#4518](https://github.com/agda/agda/issues/4518): Confusing error message if missing import
  -  [#4520](https://github.com/agda/agda/issues/4520): Better error for ambiguous BUILTIN [FROMNAT no longer working]
  -  [#4521](https://github.com/agda/agda/issues/4521): Massive increase in memory required to install Agda 2.6.1
  -  [#4526](https://github.com/agda/agda/issues/4526): Agda 2.6.1 bad performance: findProjectConfig slow in big directories
  -  [#4528](https://github.com/agda/agda/issues/4528): Internal error due to new forcing translation
  -  [#4530](https://github.com/agda/agda/issues/4530): Less normalization of goal types for instance search
  -  [#4534](https://github.com/agda/agda/issues/4534): [reflection] quote is not a defined name
  -  [#4536](https://github.com/agda/agda/issues/4536): co-pattern matching on empty record type removes body
  -  [#4538](https://github.com/agda/agda/issues/4538): changing the predefined precedence of an operator
  -  [#4543](https://github.com/agda/agda/issues/4543): Access violation on Windows on GHC 8.8.3, 8.8.4, 8.10.1 and 8.10.2
  -  [#4550](https://github.com/agda/agda/issues/4550): Documentation build: malformed code-block
  -  [#4556](https://github.com/agda/agda/issues/4556): [documentation] update hello world
  -  [#4557](https://github.com/agda/agda/issues/4557): activate github's discussions beta
  -  [#4560](https://github.com/agda/agda/issues/4560): Loss of canonicity with no-eta record and copatterns.
  -  [#4572](https://github.com/agda/agda/issues/4572): add PiSort and UnivSort to the documentation
  -  [#4576](https://github.com/agda/agda/issues/4576): quoteTC for Setω
  -  [#4580](https://github.com/agda/agda/issues/4580): No highlighting for pragmas FROMNAT, FROMNEG, FROMSTRING
  -  [#4583](https://github.com/agda/agda/issues/4583): QuickLaTeX backend does not highlight coinductive constructors as such
  -  [#4586](https://github.com/agda/agda/issues/4586): Better error message  for "Not a valid let declaration"
  -  [#4593](https://github.com/agda/agda/issues/4593): The blocking machinery seems to be broken
  -  [#4595](https://github.com/agda/agda/issues/4595): Should Setω be a type?
  -  [#4596](https://github.com/agda/agda/issues/4596): Improve pattern matching on records in telescopes
  -  [#4606](https://github.com/agda/agda/issues/4606): The combination of Cubical Agda with inductive families is logically inconsistent
  -  [#4610](https://github.com/agda/agda/issues/4610): Support Emacs 27.1
  -  [#4615](https://github.com/agda/agda/issues/4615): Enable --no-sort-comparison by default?
  -  [#4621](https://github.com/agda/agda/issues/4621): Make --rewriting infective
  -  [#4623](https://github.com/agda/agda/issues/4623): Empty where blocks should get dead code warnings
  -  [#4631](https://github.com/agda/agda/issues/4631): Non-linear patterns handled in a buggy way
  -  [#4637](https://github.com/agda/agda/issues/4637): recCon-NOT-PRINTED in termination error in connection to with
  -  [#4638](https://github.com/agda/agda/issues/4638): Erased constructors
  -  [#4649](https://github.com/agda/agda/issues/4649): Repair Agda's REPL (agda -I) to work with --safe flag
  -  [#4656](https://github.com/agda/agda/issues/4656): Function name not wrapped in `\AgdaFunction` in generated LaTeX
  -  [#4662](https://github.com/agda/agda/issues/4662): Current module contents
  -  [#4665](https://github.com/agda/agda/issues/4665): Documentation: add install instructions for stack
  -  [#4671](https://github.com/agda/agda/issues/4671): Weird error message on case-insensitive file systems
  -  [#4679](https://github.com/agda/agda/issues/4679): Cubical: giving seems to skip the boundary condition check for extended lambdas
  -  [#4681](https://github.com/agda/agda/issues/4681): Get rid of auto-inlining?
  -  [#4684](https://github.com/agda/agda/issues/4684): Type error due to --no-syntactic-equality
  -  [#4687](https://github.com/agda/agda/issues/4687): Instance search fails with two equal candidates
  -  [#4704](https://github.com/agda/agda/issues/4704): Case-split generates invalid code
  -  [#4707](https://github.com/agda/agda/issues/4707): Just warn when `using` directive has repetitions
  -  [#4721](https://github.com/agda/agda/issues/4721): de Bruijn index out of scope when using rewriting
  -  [#4727](https://github.com/agda/agda/issues/4727): Meta-variable solutions contain subterms with the wrong modality
  -  [#4735](https://github.com/agda/agda/issues/4735): primShowQName creates not-in-scope names
  -  [#4737](https://github.com/agda/agda/issues/4737): Turn error `Hiding ... has no effect` into a warning
  -  [#4750](https://github.com/agda/agda/issues/4750): Unification failure in 2.6.1 and the master branch
  -  [#4752](https://github.com/agda/agda/issues/4752): Panic on unbound variable with pattern synonym
  -  [#4768](https://github.com/agda/agda/issues/4768): De Bruijn index @0 in error "Not a finite domain"
  -  [#4769](https://github.com/agda/agda/issues/4769): mergeEqualPs ignores Name and ArgInfo of merged-in patterns
  -  [#4772](https://github.com/agda/agda/issues/4772): C-u C-u C-c C-? should show all goals normalized (Cmd_metas)
  -  [#4773](https://github.com/agda/agda/issues/4773): Missing does-not-export warning for `open` directive for parametrised module
  -  [#4775](https://github.com/agda/agda/issues/4775): Internal error when trying to use incorrect lambda syntax to pattern match
  -  [#4784](https://github.com/agda/agda/issues/4784): Make erasure compatible with univalence
  -  [#4795](https://github.com/agda/agda/issues/4795): Build "agda-tests" fails using dynamic linking
  -  [#4815](https://github.com/agda/agda/issues/4815): Current master fails compilation: binding for 'error' shadows the existing binding
  -  [#4828](https://github.com/agda/agda/issues/4828): Symlinks are incorrectly followed during compilation
  -  [#4833](https://github.com/agda/agda/issues/4833): Internal error: cannot type-check file
  -  [#4851](https://github.com/agda/agda/issues/4851): BUILTIN SIGMA and --type-in-type
  -  [#4852](https://github.com/agda/agda/issues/4852): First load the file
  -  [#4857](https://github.com/agda/agda/issues/4857): Instance argument is printed as explicit argument
  -  [#4869](https://github.com/agda/agda/issues/4869): Internal error at src/full/Agda/TypeChecking/Serialise/Instances/Internal.hs:147
  -  [#4880](https://github.com/agda/agda/issues/4880): Non-dependent, irrelevant, nameless arguments aren't accepted in arrows
  -  [#4882](https://github.com/agda/agda/issues/4882): Missing `reduce` in `literalStrategy`
  -  [#4888](https://github.com/agda/agda/issues/4888): "Illegal declaration(s) before top-level module" in Agda 2.6.1
  -  [#4909](https://github.com/agda/agda/issues/4909): Rewrite rule not accepted with --no-fast-reduce
  -  [#4924](https://github.com/agda/agda/issues/4924): Instance resolution loops infinitely even when an instance is available
  -  [#4925](https://github.com/agda/agda/issues/4925): Too aggressive literal overloading
  -  [#4928](https://github.com/agda/agda/issues/4928): Internal error checking cubical library
  -  [#4929](https://github.com/agda/agda/issues/4929): Regression in 2.6.1 connected to forcing translation (internal error)
  -  [#4944](https://github.com/agda/agda/issues/4944): Generalize: stuck on constraint ↑ i =< ↑ (↑ i) : Size
  -  [#4946](https://github.com/agda/agda/issues/4946): Size polarity brittle with generalization
  -  [#4949](https://github.com/agda/agda/issues/4949): Cubical: internal error in eta-expansion under constraints
  -  [#4950](https://github.com/agda/agda/issues/4950): Range too large in complaint about missing definitions
  -  [#4951](https://github.com/agda/agda/issues/4951): Data types in Setω are treated as non-fibrant
  -  [#4952](https://github.com/agda/agda/issues/4952): Incorrect HTML generated for renaming clause
  -  [#4962](https://github.com/agda/agda/issues/4962): JS backend: bugs involving "null"
  -  [#4967](https://github.com/agda/agda/issues/4967): Crazy bug when defining Ord instances for Int
  -  [#4970](https://github.com/agda/agda/issues/4970): `variable` use adds explicit argument
  -  [#4975](https://github.com/agda/agda/issues/4975): "no such meta variable" when calling `C-u C-c C-;`
  -  [#4982](https://github.com/agda/agda/issues/4982): Internal error related to Cubical Agda
  -  [#4986](https://github.com/agda/agda/issues/4986): Pattern matching allows you to turn `(x y : A) -> A` into `(@0 x y : A) -> A`
  -  [#4995](https://github.com/agda/agda/issues/4995): No Cycle should not look under lambdas.
  -  [#4998](https://github.com/agda/agda/issues/4998): Make case in clause with instance projection does not work
  -  [#4999](https://github.com/agda/agda/issues/4999): `primStringFromList` is not injective because of surrogate code points
  -  [#5002](https://github.com/agda/agda/issues/5002): Bad JavaScript generated
  -  [#5005](https://github.com/agda/agda/issues/5005): Add flag to print AGDA_DIR and exit
  -  [#5029](https://github.com/agda/agda/issues/5029): One can override --safe
  -  [#5033](https://github.com/agda/agda/issues/5033): Internal error related to @tick
  -  [#5048](https://github.com/agda/agda/issues/5048): Disturbing names in normalised reflected type
  -  [#5064](https://github.com/agda/agda/issues/5064): Give more information in error "Pattern matching on no-eta record types is by default not allowed"
  -  [#5065](https://github.com/agda/agda/issues/5065): The termination checker is too liberal
  -  [#5079](https://github.com/agda/agda/issues/5079): Deep pattern-matching is sometimes allowed for erased arguments
  -  [#5093](https://github.com/agda/agda/issues/5093): Weird instance propagation between parameterised modules
  -  [#5112](https://github.com/agda/agda/issues/5112): `make install-fix-whitespace` shouldn't use the `stack-X.Y.Z.yaml` files used for Agda
  -  [#5128](https://github.com/agda/agda/issues/5128): getDefinition sometimes loses patterns
  -  [#5133](https://github.com/agda/agda/issues/5133): Current master fails LaTeX-related tests
  -  [#5140](https://github.com/agda/agda/issues/5140): test/LaTeXAndHTML/succeed contains failing tests
  -  [#5146](https://github.com/agda/agda/issues/5146): v2.6.1.2 does not contain MAlonzo/RTE/Float.hs
  -  [#5161](https://github.com/agda/agda/issues/5161): No error location for error in imported module when .agdai file exists
  -  [#5167](https://github.com/agda/agda/issues/5167): Fix broken compatibility with agda-bench
  -  [#5168](https://github.com/agda/agda/issues/5168): User manual: Missing instructions for installing Agda from Hackage using stack
  -  [#5176](https://github.com/agda/agda/issues/5176): `mutual` is deprecated in doc
  -  [#5204](https://github.com/agda/agda/issues/5204): Investigate highlighting failures
  -  [#5205](https://github.com/agda/agda/issues/5205): acmart examples in (user-manual) fail to build with latest TeXLive
  -  [#5207](https://github.com/agda/agda/issues/5207): Agda generated code does not type-check with GHC 9.0
  -  [#5210](https://github.com/agda/agda/issues/5210): Internal error
  -  [#5230](https://github.com/agda/agda/issues/5230): When `stack.yaml` exists, `make` calls `stack`, even on `make debug`
  -  [#5231](https://github.com/agda/agda/issues/5231): Problems compiling hello-world.agda
  -  [#5237](https://github.com/agda/agda/issues/5237): `__IMPOSSIBLE__` from Agda.TypeChecking.Substitute
  -  [#5238](https://github.com/agda/agda/issues/5238): Rewrites are conjuring elements out of thin air
  -  [#5245](https://github.com/agda/agda/issues/5245): An infinite loop?
  -  [#5250](https://github.com/agda/agda/issues/5250): Change of warning options ignored
  -  [#5251](https://github.com/agda/agda/issues/5251): @0 annotation on lambda ignored
  -  [#5252](https://github.com/agda/agda/issues/5252): Internal error when case splitting pattern-lambda with higher rank type
  -  [#5286](https://github.com/agda/agda/issues/5286): Wrong error location with do notation and parse error in lhs
  -  [#5288](https://github.com/agda/agda/issues/5288): Very weird behaviour with compiled Data.Nat.Show.readMaybe
  -  [#5313](https://github.com/agda/agda/issues/5313): Documentation for internal level properties
  -  [#5314](https://github.com/agda/agda/issues/5314): Warn about abstract definitions without type signatures
  -  [#5317](https://github.com/agda/agda/issues/5317): The reflection machinery should support quantities
  -  [#5326](https://github.com/agda/agda/issues/5326): The highlighting code should be optimised
  -  [#5334](https://github.com/agda/agda/issues/5334): Meta-variable in constructor type busts interleaved mutual
  -  [#5335](https://github.com/agda/agda/issues/5335): Incorrect id attributes for local modules inside local modules
  -  [#5336](https://github.com/agda/agda/issues/5336): `data Foo constructor {cs : ts}` notation in `interleaved mutual`
  -  [#5339](https://github.com/agda/agda/issues/5339): `constructor` blocks do not tolerate overloading in same block
  -  [#5341](https://github.com/agda/agda/issues/5341): Do not make context variables non-erased
  -  [#5356](https://github.com/agda/agda/issues/5356): `interleaved mutual`: `data _ where` instead of `constructor`
  -  [#5358](https://github.com/agda/agda/issues/5358): tactic annotation on record field of function type drops domain in copattern definition
  -  [#5367](https://github.com/agda/agda/issues/5367): Parser regression involving `with` and `let`
  -  [#5370](https://github.com/agda/agda/issues/5370): Inconsistency in agda --help
  -  [#5375](https://github.com/agda/agda/issues/5375): Efficient conversion between interaction points and meta-variables
  -  [#5410](https://github.com/agda/agda/issues/5410): Module applications in where clauses of erased definitions yield non-erased code
  -  [#5419](https://github.com/agda/agda/issues/5419): Missing licences?
  -  [#5424](https://github.com/agda/agda/issues/5424): Internal error in v2.6.2 release candidate 1
  -  [#5434](https://github.com/agda/agda/issues/5434): The user manual's explanation of how erasure is checked for constructors does not match the implementation
