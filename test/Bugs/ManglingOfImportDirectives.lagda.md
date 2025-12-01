---
title: Premature mangling of import directives
author: Andreas Abel
date: 2025-12-01
---

# Reproducer

```agda
open import Agda.Builtin.Nat
  using (Bool) renaming (true to tt)
  using (false) renaming (if to when)
```

# Current behavior

Current warning
```error
warning:  -W[no]ModuleDoesntExport
The module Agda.Builtin.Nat doesn't export the following:
  Bool
  false
  true
  if
when scope checking the declaration
  open import Agda.Builtin.Nat using (Bool; false)
                               renaming (true to tt; if to when)
```

# Issue:

The `when scope checking the declaration`  should reproduce the original import statement
without aggregation of the using and renaming.

# Expected behavior

The following would be acceptable:
```error
open import Agda.Builtin.Nat
  using (Bool)
  renaming (true to tt)
  using (false)
  renaming (if to when)
```

# How this issue should be fixed

Currently, the mangling of import directives happens already in `Parser.y`
using the `Monoid` instance of `C.ImportDirective`.
```happy
-- Import directives
ImportDirective :: { ImportDirective }
ImportDirective
  : ImportDirective1 ImportDirective { $1 <> $2 }
  | {- empty -}                      { mempty }
```
Rather, a possibly empty list of `C.ImportDirective` should be kept around
in the `Declarations` of `Agda.Syntax.Concrete` (short: `C`).
```haskell
type ImportDirectives = [ImportDirective]

data Declaration
  = ...
  | Open        KwRange QName ImportDirectives
  | Import      OpenShortHand KwRange QName (Either AsName RawOpenArgs) ImportDirectives
```
Also in `Agda.Syntax.Concrete.Definitions.Types`:
```haskell
data NiceDeclaration
  = ...
  | NiceOpen KwRange QName ImportDirectives
  | NiceImport OpenShortHand KwRange QName (Either AsName RawOpenArgs) ImportDirectives
```
This will have the effect that when printing the trace `ScopeCheckDeclaration NiceDeclaration`
(see `Call` in `Agda.TypeChecking.Monad.Base`),
will print the import directives separately as the user wrote them.

The mangling of the import directives should then only happen in the scope checker in `Agda.Syntax.Translation.ConcreteToAbstract`.

# Testsuite

The reproducer should he added to as `.agda` file to `test/Succeed` together with the `.warn` file which is the golden value.
The `.agda` file should contain a date, a link to this issue and an explaination of what is tested and what the expected response of Agda is.

# Documentation

The fix does not require a changelog entry nor changing of the documentation.
