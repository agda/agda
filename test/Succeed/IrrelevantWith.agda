-- Andreas, 2012-04-18 make sure with functions of irrelevant functions
-- are also irrelevant
module IrrelevantWith where

import Common.Level
open import Common.Irrelevance

.unsq : ∀ {a}{A : Set a} → Squash A → A
unsq sq with Set
... | _ = unsquash sq
