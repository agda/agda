-- Andreas, 2013-02-27
module Issue385 where

import Common.Level
open import Common.Equality

loop : ∀ {A}{x : A} → x ≡ x
loop = loop

bad : Set
bad rewrite loop = ?
-- this used to loop, but should no longer, instead:

-- Cannot rewrite by equation of type {A : Set _3} {x : A} → x ≡ x
-- when checking that the clause bad rewrite loop = ? has type Set
