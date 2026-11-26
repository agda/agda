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

Builtins
--------

* Binding the `BUILTIN REWRITE` relation will now reduce the name before binding it.
  This means you can now use an alias to another type as the rewrite relation
  (see https://github.com/agda/agda/issues/6697).

* Agda inserts a hidden lambda into an expression `e` that is checked against a
  type of the form `{x : A} → B` (e.g. `refl` against `{x : A} → x ≡ x`).  This
  decision is made from the weak head normal form of the expected type and is
  irreversible, so it used to be made wrongly when that type was still blocked
  -- in particular when it was blocked by an instance argument whose resolution
  had been deferred while the arguments of an application were being checked.
  Agda now postpones the type checking problem in this situation.
  For example, this now succeeds:
  ```agda
  open import Agda.Builtin.Equality
  open import Agda.Builtin.FromNat
  open import Agda.Builtin.Nat
  open import Agda.Builtin.Unit

  instance
    NumberNat : Number Nat
    NumberNat = record { Constraint = λ _ → ⊤; fromNat = λ n → n }

  Hidden : Nat → Set
  Hidden zero    = 0 ≡ 0
  Hidden (suc n) = {x : Nat} → Hidden n

  solve : (n : Nat) → Hidden n → Set
  solve n hyp = Nat

  bad : Set
  bad = solve 1 refl   -- used to require `λ {_} → refl`
  ```
  Here the numeral `1` elaborates to `fromNat 1 ⦃ i ⦄ ⦃ c ⦄`, so the expected
  type `Hidden (fromNat 1 ⦃ i ⦄ ⦃ c ⦄)` of `refl` is blocked on the instance
  meta `i`.
  (Issue [#8749](https://github.com/agda/agda/issues/8749);
  this is a facet of the more general issue
  [#1079](https://github.com/agda/agda/issues/1079), which is not fixed.)

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
