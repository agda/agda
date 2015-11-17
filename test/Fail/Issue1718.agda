-- Andreas, 2015-11-17, issue reported by Martin Stone Davis

module _ where

module Sub (let open import oops) where

-- WAS: internal error

-- EXPECTED: Not a valid let-declaration
--   when scope checking the declaration
--     module Sub (let open import oops) where
