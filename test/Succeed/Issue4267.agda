-- Andreas, 2019-12-08, issue #4267, reported and test case by csattler

-- Problem: definitions from files (A1) imported by a module
-- (Issue4267) may leak into the handling of an independent module
-- (B).

-- The root issue here is that having a signature stImports that
-- simply accumulates the signatures of all visited modules is
-- unhygienic.

module Issue4267 where

open import Issue4267.A0
open import Issue4267.A1 -- importing A1 here (in main) affects how B is type-checked
open import Issue4267.B

-- After the fix of #4267, these imports should succeed without unsolved metas.
