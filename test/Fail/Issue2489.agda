
data ⊤ : Set where
  t : ⊤

data ⊤⊤ : Set where
  tt : ⊤⊤

module M (x : ⊤⊤) where

  instance
    top : ⊤
    top = t

search : ∀ {ℓ} {t : Set ℓ} {{_ : t}} → t
search {{p}} = p

-- no instance is in scope, and none is found
-- correct : ⊤
-- correct = search

someDef : ⊤
someDef = top
  where
    open M tt

-- incorrect! there should be no instance available.
leak : ⊤
leak = search
