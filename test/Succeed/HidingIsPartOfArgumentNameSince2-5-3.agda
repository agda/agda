-- Andreas, 2019-01-20, re #2597.
-- Undocumented language change introduced by patch 31a5982f38 (released in 2.5.3):
-- Hiding of argument now treated as part of name when inserting implicits.

-- Patch introduced in src/full/Agda/TypeChecking/Implicit.hs
--
-- ... | x == y && sameHiding hidingx a = impInsert $ reverse hs
--     | x == y && sameHiding hidingx a = BadImplicits
--
-- Intended was most likely
--     | x == y && not (sameHiding hidingx a) = BadImplicits
--
-- The patch makes this code legal:

test : {{X : Set}} {X : Set} → Set
test {X = X} = X

-- Succeeds in 2.5.3.
-- Fails in 2.5.2 with error:
-- Unexpected implicit argument
-- when checking that the clause test {X = X} = X has type
-- {{X : Set}} {X = X₁ : Set} → Set
