---
title: `UnusedImports` warnings concerning modules
author: Andreas Abel
date: 2025-12-08
---

```agda
{-# OPTIONS -WUnusedImports #-}

-- {-# OPTIONS -v warning.unusedImports:60 #-}

module _ where
```

# Unused module in `using` directive.

```agda
open import Agda.Builtin.Equality using (module _≡_)
```
This should warn about the unused `module _≡_` and highlight it.

# Unused module in `renaming` directive.
```agda
open import Agda.Builtin.Equality using () renaming (module _≡_ to Eq)
```
This should warn about the unused module `Eq` and highlight it.


# A module that just exports an unused module

```agda
module Parent where
  module Child where
   postulate A : Set

module Mod1 where
  open Parent
```
The `open` should be reported as redundant.

# A module that just exports an module used in qualification

```agda
module Mod2 where
  open Parent
  postulate x : Child.A
```
There should be no warning for this `open` statement

# Importing just a module but this one is used

```agda
import Agda.Builtin.Nat

Nat = Agda.Builtin.Nat.Nat

module Nat1 where
  open Agda.Builtin.Nat using (module Nat)  -- no warning
  open Nat -- no warning

  plus : (x y : Nat) → Nat
  plus zero y = y
  plus (suc x) y = suc (plus x y)
```
No warnings about unused imports expected here.

# Using a module in qualified names

```agda
module Nat2 where
  open Agda.Builtin.Nat using (module Nat)  -- no warning

  plus : (x y : Nat) → Nat
  plus Nat.zero y = y
  plus (Nat.suc x) y = Nat.suc (plus x y)
```
The imported module `Nat` is used qualified so not redundantly imported.
