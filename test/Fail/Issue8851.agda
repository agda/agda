-- Andreas, 2026-10-19, issue #8851
-- Names bound by unquoteDecl that the meta-program does not declare
-- should be reported, rather than causing a panic.

module Issue8851 where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

doNothing : TC ⊤
doNothing = returnTC tt

unquoteDecl bang = doNothing
