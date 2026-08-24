-- Andreas, 2026-08-24, re issue #8625

module AnonymousRecConstrModuleApp where

-- The Record.constructor syntax refers to the record module Record,
-- but currently has some special status.
-- In accordance to #4189, the record constructor does not live in the record module.
-- Thus, applying the record module to arguments, does not give access to the constructor.

record R : Set₁ where
  field x : Set

module M = R

_ = M.constructor

-- Fails, although one could image a change of the semantics that makes this work.
-- error: [NotInScope]
-- Not in scope:
--   M.constructor
