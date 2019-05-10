{-# OPTIONS --rewriting --confluence-check #-}

postulate _↦_ : ∀ {a} {A : Set a} → A → A → Set
{-# BUILTIN REWRITE _↦_ #-}

open import Agda.Primitive

postulate
  mekker : Level → Level → Set
  moomoo : Level → Set → Set
  rew : (a b : Level) → moomoo (a ⊔ b) (mekker a b) ↦ (Level → Level)

{-# REWRITE rew #-}

works : {a b : Level} → moomoo (a ⊔ b) (mekker a b) → Level
works f = f lzero

fails : {a : Level} → moomoo a (mekker a a) → Level
fails f = f lzero
