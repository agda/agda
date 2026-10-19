module Issue3218 where

postulate
  A   : Set
  _≤_ : A → A → Set
  _•_ : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c

data Tree : Set where
  node : Tree → Tree

data _⊑_ : Tree → Tree → Set where
  trans : ∀ {a b c} → a ⊑ b → b ⊑ c → a ⊑ c

record Fun : Set where
  field ap  : Tree → A
  field map : ∀ {T U} → T ⊑ U → ap T ≤ ap U
open Fun

-- Accepted
get : Tree → A
get (node T) = get T

Get : Fun
ap  Get = get
map Get (trans T≤U U≤V) = map Get T≤U • map Get U≤V

-- Previously rejected
NoGet : Fun
ap  NoGet (node T)        = ap  NoGet T
map NoGet (trans T≤U U≤V) = map NoGet T≤U • map NoGet U≤V
