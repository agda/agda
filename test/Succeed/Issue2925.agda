{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Equality

{-# BUILTIN REWRITE _≡_ #-}

postulate
  X   : Set₁
  rew : X ≡ Set

{-# REWRITE rew #-}
{-# REWRITE rew #-}
