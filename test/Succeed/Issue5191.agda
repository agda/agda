-- This code is closely based on code due to Andy Morris.

data _≡⁰_ {A : Set} (@0 x : A) : @0 A → Set where refl : x ≡⁰ x
data _≡ʷ_ {A : Set} (@ω x : A) : @ω A → Set where refl : x ≡ʷ x

works : ∀ {A} {@0 x y : A} → x ≡⁰ y → x ≡ʷ y
works refl = refl

also-works : ∀ {A} {@0 x y : A} → x ≡⁰ y → x ≡ʷ y
also-works {x = x} refl = refl {x = x}
