-- {-# OPTIONS -v interaction:100 #-}
module Issue810 where

postulate
  T : Set → Set

introHid : {A : Set} → T A
introHid = {!!}

data Sg {A : Set} : A → Set where
  sg : (a : A) → Sg a

intro : ∀ {A}{a : A} → Sg a
intro = {!!}

intro′ : ∀ {A}(a : A) → Sg a
intro′ = {!!}
