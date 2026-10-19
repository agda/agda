module PatternSynonymImports where

open import PatternSynonyms renaming (z to zzz)

pattern myzero = zzz
two = ss zzz


list : List ℕ
list = 1 ∷ []

-- Andreas, 2026-02-22
-- Overloading of pattern synonyms is allowed.

pattern sz = suc zzz

-- This overloaded pattern synonym resolves to the same thing
-- than its original definition, so this should be fine.

overloaded : ℕ
overloaded = sz
