module Issue1760g where

data ⊥ : Set where

{-# NO_POSITIVITY_CHECK #-}
{-# NON_TERMINATING     #-}
mutual
  record U : Set where
    pattern; constructor roll
    field ap : U → U

  lemma : U → ⊥
  lemma (roll u) = lemma (u (roll u))

  bottom : ⊥
  bottom = lemma (roll λ x → x)
