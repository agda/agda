module IrrelevantProjections where
import Common.Irrelevance  

record [_] (A : Set) : Set where
  field
    .inflate : A

open [_] using (inflate)

-- Should fail, since proj isn't declared irrelevant.
proj : ∀ {A} → [ A ] → A
proj x = inflate x
