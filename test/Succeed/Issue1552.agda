{-# OPTIONS --rewriting --confluence-check #-}

-- {-# OPTIONS -v rewriting:100 #-}

postulate
  _↦_ : ∀ {i} {A : Set i} → A → A → Set i

{-# BUILTIN REWRITE _↦_ #-}

postulate
  Unit : Set
  tt : Unit

module _ {i} (P : Unit → Set i) (tt* : P tt) where

  postulate
    Unit-elim : (x : Unit) → P x
    Unit-β : Unit-elim tt ↦ tt*
  {-# REWRITE Unit-β #-}
