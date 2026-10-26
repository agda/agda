{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality

_↝_ = _≡_

{-# BUILTIN REWRITE _↝_ #-}

postulate
  X : Set₁
  rew : X ↝ Set

{-# REWRITE rew #-}
