module Issue363 where

infixl 0 _>>=_

postulate
  A     : Set
  x     : A
  _>>=_ : A → (A → A) → A
  P     : A → Set

lemma : P ((x >>= λ x → x) >>= λ x → x)
lemma = {!!}

-- The type of the goal above was printed as follows:
--
--   P (x >>= λ x' → x' >>= λ x' → x')
--
-- This is not correct.
