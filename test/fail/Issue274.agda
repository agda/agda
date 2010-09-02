module Issue274 where

-- data ⊥ : Set where

record U : Set where
  constructor roll
  field ap : U → U

-- lemma : U → ⊥
-- lemma (roll u) = lemma (u (roll u))

-- bottom : ⊥
-- bottom = lemma (roll λ x → x)
