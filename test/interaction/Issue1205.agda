-- Andreas, 2014-06-27, issue raised by fsfbugs
-- {-# OPTIONS -v interaction.give:10 -v tc:20 -v tc.conv.sort:30 #-}

open import Common.Level

record R (p r : Level) : Set (lsuc (p ⊔ r)) where
  field
    P   : Set p
    _~_ : P -> P -> Set r
    f   : (p p' : P) -> {!p ~ p'!}  -- Give (p ~ p') here!


-- PROBLEM WAS:
-- When issuing C-c C-SPC, Agda complains
--   Set (r ⊔ p) != Set (suc r ⊔ suc p)
-- even though removing the hole manually (by removing '{!' and '!}')
-- gives a well-typed definition.

-- REASON WAS:
-- Conversion.leqSort produced equality rather than subtyping constraint
-- upon postponement:
--   does (f : (p p' : P) → ?0 p r P _~_ p p') → f
--   of sort Setω
--   fit in Set (lsuc r ⊔ lsuc p) ?
--   adding constraint [0] dLub (Set p)
--                       (λ p → dLub (Set p) (λ p' → Set (_4 p r P _~_ p p')))
--                       == Set (lsuc r ⊔ lsuc p)

-- WORKS NOW
