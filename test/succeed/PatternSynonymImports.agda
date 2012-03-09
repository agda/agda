module PatternSynonymImports where

open import PatternSynonyms renaming (z to zzz)

pattern myzero = zzz
two = ss zzz


list : List ℕ
list = 1 ∷ []