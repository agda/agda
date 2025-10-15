{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Issue8068 where

postulate
  O : Set
  Q : Set
  d : Q → O
  c : Q → O
  Oᴰ : O → Set

data Path : O → O → Set where
  [] : ∀ {a} → Path a a
  _∷_ : ∀ {a} g (p : Path (c g) a) → Path (d g) a

postulate
  Hᴰ : ∀ {o o'}(f : Path o o') → Oᴰ o → Oᴰ o' → Set

foo : ∀ (ıo : ∀ a → Oᴰ a) (ıh : {!   !}) {a b}(f : Path a b) → Hᴰ f (ıo a) (ıo b)
foo ıo ıh []      = {!!}
foo ıo ıh (g ∷ f) = {!!}
