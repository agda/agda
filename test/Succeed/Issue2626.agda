-- Andreas, 2017-07-05, issue #2626 raised by cartazio
-- shrunk by gallais

-- There was an assignTerm inspite of
-- dontAssignMetas (issued by checking inequations involving ⊔ˢ)

-- {-# OPTIONS -v tc:45 #-}

{-# OPTIONS --allow-unsolved-metas #-}

module Issue2626 where

open import Agda.Builtin.Equality
open import Agda.Builtin.Size

data D : (sz : Size) → Set where
  c : (q s : Size) → D (q ⊔ˢ s)

postulate
  foo : c _ _ ≡ c _ _
