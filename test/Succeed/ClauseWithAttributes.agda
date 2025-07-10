-- Andreas, 2025-07-03, issue #7987
-- Attributes are now supported on function clauses.

{-# OPTIONS --erasure #-}

@0 id : (A : Set) → A → A
@0 id A x = x

-- Should succeed.

S : Set₁
@(tactic _) S = Set

-- Expected warning: -W[no]MisplacedAttributes
-- Ignoring tactic attribute, illegal in function clauses
