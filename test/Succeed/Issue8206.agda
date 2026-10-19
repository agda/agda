-- Andreas, 2025-11-15, issue #8206
-- "interleaved mutual" did not catch disallowed parts
-- of parameters in data/record definition.

interleaved mutual

  data S (A : Set) : Set

  data S (A : Set1) where
     c : A → S A

-- Expected: warning: -W[no]InvalidDataOrRecDefParameter
-- Ignoring parameter type in data definition
-- (note: parameters may not repeat information from signature)
