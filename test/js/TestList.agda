open import Common.Prelude
open import TestHarness
open import TestBool using ( not; _∧_ ; _↔_ )

module TestList where

_++_ : ∀ {X} → List X → List X → List X
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

revApp : ∀ {X} → List X → List X → List X
revApp []       ys = ys
revApp (x ∷ xs) ys = revApp xs (x ∷ ys)

reverse : ∀ {X} → List X → List X
reverse xs = revApp xs []

_≟_ : List Bool → List Bool → Bool
[]       ≟ []       = true
(x ∷ xs) ≟ (y ∷ ys) = (x ↔ y) ∧ (xs ≟ ys)
_        ≟ -        = false

[tt] = true ∷ []
[ff] = false ∷ []
[tt,ff] = true ∷ [ff]
[ff,tt] = false ∷ [tt]
[ff,tt,ff] = false ∷ [tt,ff]

tests : Tests
tests _ = (
    assert ([] ≟ []) "[]=[]" ,
    assert (not ([tt] ≟ [ff])) "[tt]≠[ff]" ,
    assert (([] ++ [tt]) ≟ [tt]) "[]++[tt]=[tt]" ,
    assert (([tt] ++ []) ≟ [tt]) "[tt]++[]=[tt]" ,
    assert (([tt] ++ [ff]) ≟ [tt,ff]) "[tt]++[ff]=[tt,ff]" ,
    assert (([ff,tt] ++ [ff]) ≟ [ff,tt,ff]) "[ff,tt]++[ff]=[ff,tt,ff]" ,
    assert (not (([ff] ++ [tt]) ≟ [tt,ff])) "[ff]++[tt]≠[tt,ff]" ,
    assert (not (([tt] ++ [tt]) ≟ [tt,ff])) "[tt]++[tt]≠[tt,ff]" ,
    assert (reverse [tt,ff] ≟ [ff,tt]) "rev[tt,ff]=[ff,tt]" ,
    assert (reverse (reverse [tt,ff]) ≟ [tt,ff]) "rev(rev[tt,ff])=[tt,ff]" ,
    assert (not (reverse [tt,ff] ≟ [tt,ff])) "rev[tt,ff]≠[tt,ff]"
  )