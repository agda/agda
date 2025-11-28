-- Andreas, 2025-11-18, issue #8037
-- Auxiliary module imported by Issue8037Deadcode
-- that exports a record module created by module application.

module Issue8037DeadcodeA where

  record Whatever (A : Set) : Set where
    no-eta-equality
    field go : A → A

  module M (A : Set) = Whatever {A → A}
  open M public
