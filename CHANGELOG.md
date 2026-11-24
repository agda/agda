Release notes for Agda version 2.10.0
=====================================

Highlights
----------

Installation
------------

* Agda supports GHC versions 9.2.8 to 9.14.1.

* New: GitHub releases include a statically linked Linux ARM64 binary
  (see [#7603](https://github.com/agda/agda/issues/7603)).

Pragmas and options
-------------------

Errors
------

Warnings
--------

* New warning `WrongAssociativity` suggests `infixr` for prefix operators
  declared with `infixl` and `infixl` for postfix operators declared with
  `infixr`.

* Warning `ShadowingInTelescope` is now on by default.

* `InstanceNoOutputTypeName` and `InstanceArgWithExplicitArg` now also warn
  about instance `variable` declarations and anonymous instance arguments
  in function types.

* New warning `PragmaCompileDefined` when a `COMPILE GHC` pragma overrides
  the definition of a (non-abstract) function.

Syntax
------

Changes to the Agda syntax.

Language
--------

Changes to type checker and other components defining the Agda language.

* (**BREAKING**) `--sized-types`: Matching a size against a successor
  (successor style of sized types, e.g. `suc : ∀ {i} → Nat i → Nat (↑ i)`)
  now only provides termination evidence if the type of the recursive function
  is _upper semi-continuous_ in that size
  ([issue #8829](https://github.com/agda/agda/issues/8829)).
  Previously, this check was missing, which allowed a proof of `⊥`.
  For instance, the following is now rejected, because the argument type
  `∀ n → IsNat i n` is not lower semi-continuous in `i`:
  ```agda
  data IsNat : Size → Nat → Set where
    isZero : ∀ i     →             IsNat (↑ i) zero
    isSuc  : ∀ i {n} → IsNat i n → IsNat (↑ i) (suc n)

  shift : ∀ i → (∀ n → IsNat (↑ i) n) → ∀ n → IsNat i n
  shift i f n with f (suc n)
  ... | isSuc j b = b

  loop : ∀ i → (∀ n → IsNat i n) → ⊥
  loop i f with f zero
  ... | isZero j = loop j (shift j f)  -- termination error
  ```
  Admissible types include those whose argument types are sized inductive
  types, antitone, non-recursive data or record types of such,
  or functions over finite domains (such as `Bool`) into such.
  Recursion via `Size<` style sized types is well-founded and not affected.
  See the [user manual](https://agda.readthedocs.io/en/latest/language/sized-types.html#successor-style-sized-types-and-semi-continuity)
  for details.

Builtins
--------

* Binding the `BUILTIN REWRITE` relation will now reduce the name before binding it.
  This means you can now use an alias to another type as the rewrite relation
  (see https://github.com/agda/agda/issues/6697).

Reflection
----------

Library management
------------------

Interaction and emacs mode
--------------------------

* Bindings for all unicode mathematical font and other stylized variants of
  Latin letters, Greek letters, and digits, the superscript letters `𐞥ꟲꟳꟴ꟱𐞲ᶹ`,
  and the variant equality symbols `⧣﹦꞊`.

* The Emacs mode is now less eager to "pop up" the Agda information
  buffer.

Backends
--------

Issues closed
-------------

For 2.10.0, the following issues were
[closed](https://github.com/agda/agda/issues?q=is%3Aissue+milestone%3A2.10.0+is%3Aclosed)
(see [bug tracker](https://github.com/agda/agda/issues)):

### Consistency issues

### Internal errors

### Other regressions

### Other issues

Pull requests merged for 2.10.0
-------------------------------
