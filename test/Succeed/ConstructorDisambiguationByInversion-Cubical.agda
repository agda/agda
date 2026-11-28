-- The inversion map for `El` records only `Base` from its written clause.
-- The generated transport clause also makes `El wrappedTag` compute to
-- `Wrapper Base`.  Using only the recorded head would select `Base.c`.
-- Once Agda checks the equality at `wrappedTag`, the required constructor is `Wrapper.c`.

{-# OPTIONS --cubical #-}

module ConstructorDisambiguationByInversion-Cubical where

open import Agda.Primitive.Cubical using (i0 ; i1 ; primIMax ; primINeg ; primTransp)
open import Agda.Builtin.Cubical.Equiv using (_≃_ ; isEquiv ; equiv-proof)
open import Agda.Builtin.Cubical.Glue using (primGlue)
open import Agda.Builtin.Cubical.Path using (_≡_)
import Agda.Builtin.Equality as Eq using (_≡_ ; refl)
open import Agda.Builtin.Sigma using (_,_ ; fst ; snd)

idIsEquiv : ∀ {ℓ} (X : Set ℓ) → isEquiv (λ (x : X) → x)
idIsEquiv X .equiv-proof y =
  (y , λ _ → y) , λ z i → z .snd (primINeg i) , λ j → z .snd (primIMax (primINeg i) j)

ua : ∀ {ℓ} {X Y : Set ℓ} → X ≃ Y → X ≡ Y
ua {X = X} {Y = Y} e i =
  primGlue Y (λ { (i = i0) → X ; (i = i1) → Y })
             (λ { (i = i0) → e ; (i = i1) → (λ y → y) , idIsEquiv Y })

transport : ∀ {ℓ} {X Y : Set ℓ} → X ≡ Y → X → Y
transport p x = primTransp (λ i → p i) i0 x

data Base : Set where
  b : Base
  c : Base → Base

record Wrapper (X : Set) : Set where
  constructor c
  field val : X
open Wrapper

wrapEquiv : (X : Set) → X ≃ Wrapper X
wrapEquiv X .fst = c  -- The codomain is already known here, so `c` is `Wrapper.c`.
wrapEquiv X .snd .equiv-proof y =
  (y .val , λ _ → y) , λ z i →
    (z .snd (primINeg i)) .val , λ j → z .snd (primIMax (primINeg i) j)

id≡Wrapper : (λ (X : Set) → X) ≡ Wrapper
id≡Wrapper i X = ua (wrapEquiv X) i

-- Transport along this path in the universe sends `Base` to `Wrapper Base`.
wrapperPath : Set ≡ Set
wrapperPath = ua (Wrapper , transport (λ i → isEquiv (id≡Wrapper i)) (idIsEquiv Set))

data Tag : Set₁ → Set₂ where
  point : Tag Set

El : ∀ {X : Set₁} → Tag X → X
El point = Base

wrappedTag : Tag Set
wrappedTag = transport (λ i → Tag (wrapperPath i)) point

_ : El wrappedTag Eq.≡ Wrapper Base
_ = Eq.refl

select : ∀ {i : Tag Set} → El i → i Eq.≡ wrappedTag → Wrapper Base
select x Eq.refl = x

test : Wrapper Base
test = select (c b) Eq.refl  -- The equality fixes the constructor to `Wrapper.c`.
