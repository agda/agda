-- {-# OPTIONS -v tc.lhs.unify:100 #-}
module Issue811 where

module ParamIndex where
  -- Report by stevan:
  -- When case-splitting, I think dots end up at the wrong places,
  -- consider:

  data _≡_ {A : Set}(x : A) : A → Set where
    refl : x ≡ x

  -- If you case-split on p in:
  dot : ∀ {A}(x : A)(y : A) → x ≡ y → Set
  dot x y p = {!p!}

  {- You get:
  dot′ : ∀ {A}(x y : A) → x ≡ y → Set
  dot′ .y y refl = {!!}

  -- This seems the wrong way around to me, because we say that the first
  -- argument has to be something, namely y, before that something has
  -- been introduced.

  -- If I'd do the case-splitting manually, I would write:
  dot″ : ∀ {A}(x y : A) → x ≡ y → Set
  dot″ x .x refl = {!!}
  -}

  -- Andreas, 2013-03-05 This is indeed what you get now, since
  -- Agda now prefers the more left variables.

  -- Unfortunately, this leads to bad behavior in this case:
  dot1 : ∀ {A}{x : A}(y : A) → x ≡ y → Set
  dot1 y p = {!p!}

  -- This one works nicely
  dot2 : ∀ {A}(x : A){y : A} → x ≡ y → Set
  dot2 x p = {!p!}

module AllIndices where

  data _≡_ {A : Set} : A → A → Set where
    refl : ∀ x → x ≡ x

  dot : ∀ {A}(x : A)(y : A) → x ≡ y → Set
  dot x y p = {!p!}

  -- Same problem here:
  dot1 : ∀ {A}{x : A}(y : A) → x ≡ y → Set
  dot1 y p = {!p!}

  dot2 : ∀ {A}(x : A){y : A} → x ≡ y → Set
  dot2 x p = {!p!}
