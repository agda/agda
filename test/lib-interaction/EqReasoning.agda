open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

test : 0 ≡ 0
test = begin
  0 ≡⟨ {!!} ⟩
  0
  ∎

-- WAS: Goal is garbled:
--
-- ?0 : (.Relation.Binary.Setoid.preorder (setoid ℕ)
--  .Relation.Binary.Preorder.∼ 0)
-- 0

-- EXPECTED: Nice goal:
--
-- ?0 : 0 ≡ 0
