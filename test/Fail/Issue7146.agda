-- Andreas, 2024-02-25, issue #7146, printer bugs:
-- Missing parenthesis in domain-free module parameter with cohesion.
-- Missing printing of @lock attribute.

{-# OPTIONS --cohesion --erasure --guarded #-}

import Agda.Builtin.Bool
open import Agda.Builtin.Sigma

primitive
  primLockUniv : Set₁

postulate
  Tick : primLockUniv
  Foo  : @♭ Set → Tick → Set

module @0 Bool where

  -- Trigger an error here printing the module telescope, e.g.
  -- "Not supported: open public in hard compile-time mode".

  open module M (@♭ A) (@lock l) (_ : Foo A l) {@ω B = C : Set} {D : C → Set} {p@(u , v) : Σ C D}
    = Agda.Builtin.Bool public

-- Expect to fail.
--
-- Error was:
-- when checking the module application
-- module M @♭ A l (_ : Foo A l) ...
--
-- This misprints the module parameters, correct is:
-- module M (@♭ A) (@lock l) ...
--
-- Should print the module telescope correctly.
