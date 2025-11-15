-- Andreas, 2025-11-15, issue #8206
-- "interleaved mutual" did not catch disallowed parts
-- of parameters in data/record definition.

interleaved mutual

  data S (A : Set) : Set

  data S (A : Set1) where
     c : A → S A

-- Expected: warning: -W[no]InvalidDataOrRecDefParameter
-- Ignoring misplaced type of parameter in data definition
