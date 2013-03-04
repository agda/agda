module Issue784.Values where

open import Data.Bool using (Bool; true; false; not)
open import Data.String public using (String; _≟_)

open import Function public
open import Data.List using (List; []; _∷_; _++_; [_]; filter) renaming (map to mapL)
open import Data.List.Any public using (Any; here; there) renaming (map to mapA; any to anyA)
open import Data.Product public using (Σ; Σ-syntax; proj₁; proj₂; _,_; _×_) renaming (map to mapΣ)
open import Data.Unit public using (⊤; Unit; unit)
open import Data.Empty public using (⊥; ⊥-elim)
open import Relation.Binary.Core public
open import Relation.Nullary.Core public
import Level

open import Relation.Binary.PropositionalEquality public hiding ([_]) renaming (cong to ≡-cong; cong₂ to ≡-cong₂)
open import Relation.Binary.PropositionalEquality.Core public renaming (sym to ≡-sym; trans to ≡-trans)

≢-sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≢ y → y ≢ x
≢-sym x≢y = x≢y ∘ ≡-sym

≡-elim : ∀ {ℓ} {X Y : Set ℓ} → X ≡ Y → X → Y
≡-elim refl p = p

≡-elim′ : ∀ {a ℓ} {A : Set a} {x y : A} → (P : A → Set ℓ) → x ≡ y → P x → P y
≡-elim′ P = ≡-elim ∘ (≡-cong P)

Named : ∀ {ℓ} (A : Set ℓ) → Set ℓ
Named A = String × A

NamedType : ∀ ℓ → Set (Level.suc ℓ)
NamedType ℓ = Named (Set ℓ)

NamedValue : ∀ ℓ → Set (Level.suc ℓ)
NamedValue ℓ = Named (Σ[ A ∈ Set ℓ ] A)

Names : Set
Names = List String

Types : ∀ ℓ → Set (Level.suc ℓ)
Types ℓ = List (NamedType ℓ)

Values : ∀ ℓ → Set (Level.suc ℓ)
Values ℓ = List (NamedValue ℓ)

names : ∀ {ℓ} {A : Set ℓ} → List (Named A) → Names
names = mapL proj₁

types : ∀ {ℓ} → Values ℓ → Types ℓ
types = mapL (mapΣ id proj₁)

infix 4 _∈_ _∉_

_∈_ : ∀ {ℓ} {A : Set ℓ} → A → List A → Set ℓ
x ∈ xs = Any (_≡_ x) xs

_∉_ : ∀ {ℓ} {A : Set ℓ} → A → List A → Set ℓ
x ∉ xs = ¬ x ∈ xs

x∉y∷l⇒x≢y : ∀ {ℓ} {A : Set ℓ} {x y : A} {l : List A} → x ∉ y ∷ l → x ≢ y
x∉y∷l⇒x≢y x∉y∷l x≡y = x∉y∷l $ here x≡y

x∉y∷l⇒x∉l : ∀ {ℓ} {A : Set ℓ} {x y : A} {l : List A} → x ∉ y ∷ l → x ∉ l
x∉y∷l⇒x∉l x∉y∷l x∈l = x∉y∷l $ there x∈l

x≢y⇒x∉l⇒x∉y∷l : ∀ {ℓ} {A : Set ℓ} {x y : A} {l : List A} → x ≢ y → x ∉ l → x ∉ y ∷ l
x≢y⇒x∉l⇒x∉y∷l x≢y x∉l (here x≡y) = x≢y x≡y
x≢y⇒x∉l⇒x∉y∷l x≢y x∉l (there x∈l) = x∉l x∈l

infix 5 _∋!_ _∈?_

_∈?_ : (s : String) (n : Names) → Dec (s ∈ n)
s ∈? [] = no λ()
s ∈? (h ∷ t) with s ≟ h
... | yes s≡h = yes $ here s≡h
... | no s≢h with s ∈? t
...        | yes s∈t = yes $ there s∈t
...        | no s∉t = no $ x≢y⇒x∉l⇒x∉y∷l s≢h s∉t

_∋!_ : Names → String → Bool
l ∋! e with e ∈? l
... | yes _ = true
... | no _ = false

infix 4 _⊆_ _⊈_

_⊆_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → Set ℓ
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

_⊈_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → Set ℓ
xs ⊈ ys = ¬ xs ⊆ ys

infixl 5 _∪_

_∪_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → List A
_∪_ = _++_

infixl 6 _∩_

_∩_ : Names → Names → Names
x ∩ y = filter (_∋!_ y) x

infixl 6 _∖_ _∖∖_

_∖_ : Names → Names → Names
_∖_ x y = filter (not ∘ _∋!_ y) x

_∖∖_ : ∀ {ℓ} {A : Set ℓ} → List (Named A) → Names → List (Named A)
_∖∖_ l n = filter (not ∘ _∋!_ n ∘ proj₁) l

filter-∈ : ∀ {ℓ} {A : Set ℓ} → List (Named A) → Names → List (Named A)
filter-∈ l n = filter (_∋!_ n ∘ proj₁) l

data NonRepetitive {ℓ} {A : Set ℓ} : List A → Set ℓ where
  [] : NonRepetitive []
  _∷_ : ∀ {x xs} → x ∉ xs → NonRepetitive xs → NonRepetitive (x ∷ xs)

infix 4 _≋_

data _≋_ {ℓ} {A : Set ℓ} : List A → List A → Set ℓ where
  refl : ∀ {l} → l ≋ l
  perm : ∀ {l} l₁ x₁ x₂ l₂ → l ≋ l₁ ++ x₂ ∷ x₁ ∷ l₂ → l ≋ l₁ ++ x₁ ∷ x₂ ∷ l₂

NonRepetitiveNames : ∀ {ℓ} {A : Set ℓ} → List (Named A) → Set
NonRepetitiveNames = NonRepetitive ∘ names

NonRepetitiveTypes : ∀ ℓ → Set (Level.suc ℓ)
NonRepetitiveTypes ℓ = Σ[ t ∈ Types ℓ ] NonRepetitiveNames t

-- lemmas

∪-assoc : ∀ {l} {A : Set l} (x y z : List A) → (x ∪ y) ∪ z ≡ x ∪ (y ∪ z)
∪-assoc [] y z = refl
∪-assoc (x ∷ xs) y z = ≡-elim′ (λ e → x ∷ e ≡ x ∷ xs ∪ (y ∪ z)) (≡-sym $ ∪-assoc xs y z) refl

≡⇒≋ : ∀ {ℓ} {A : Set ℓ} {x y : List A} → x ≡ y → x ≋ y
≡⇒≋ refl = refl

private
    ∈-perm : ∀ {ℓ} {A : Set ℓ} {x : A} (l₁ : List A) (e₁ : A) (e₂ : A) (l₂ : List A) → x ∈ l₁ ++ e₁ ∷ e₂ ∷ l₂ → x ∈ l₁ ++ e₂ ∷ e₁ ∷ l₂
    ∈-perm [] e₁ e₂ l₂ (here .{e₁} .{e₂ ∷ l₂} px) = there $ here px
    ∈-perm [] e₁ e₂ l₂ (there .{e₁} .{e₂ ∷ l₂} (here .{e₂} .{l₂} px)) = here px
    ∈-perm [] e₁ e₂ l₂ (there .{e₁} .{e₂ ∷ l₂} (there .{e₂} .{l₂} pxs)) = there $ there pxs
    ∈-perm (h₁ ∷ t₁) e₁ e₂ l₂ (here .{h₁} .{t₁ ++ e₁ ∷ e₂ ∷ l₂} px) = here px
    ∈-perm (h₁ ∷ t₁) e₁ e₂ l₂ (there .{h₁} .{t₁ ++ e₁ ∷ e₂ ∷ l₂} pxs) = there $ ∈-perm t₁ e₁ e₂ l₂ pxs

≋⇒⊆ : ∀ {ℓ} {A : Set ℓ} {x y : List A} → x ≋ y → x ⊆ y
≋⇒⊆ refl p = p
≋⇒⊆ {x = x} {y = .(l₁ ++ x₁ ∷ x₂ ∷ l₂)} (perm l₁ x₁ x₂ l₂ p) {e} e∈x = ∈-perm l₁ x₂ x₁ l₂ $ ≋⇒⊆ p e∈x

≋-trans : ∀ {l} {A : Set l} {x y z : List A} → x ≋ y → y ≋ z → x ≋ z
≋-trans p refl = p
≋-trans p₁ (perm l₁ x₁ x₂ l₂ p₂) = perm l₁ x₁ x₂ l₂ $ ≋-trans p₁ p₂

≋-sym : ∀ {l} {A : Set l} {x y : List A} → x ≋ y → y ≋ x
≋-sym refl = refl
≋-sym (perm l₁ x₁ x₂ l₂ p) = ≋-trans (perm l₁ x₂ x₁ l₂ refl) (≋-sym p)

≋-del-ins-r : ∀ {l} {A : Set l} (l₁ : List A) (x : A) (l₂ l₃ : List A) → (l₁ ++ x ∷ l₂ ++ l₃) ≋ (l₁ ++ l₂ ++ x ∷ l₃)
≋-del-ins-r l₁ x [] l₃ = refl
≋-del-ins-r l₁ x (h ∷ t) l₃ = ≋-trans p₀ p₅
  where p₀ : (l₁ ++ x ∷ h ∷ t ++ l₃) ≋ (l₁ ++ h ∷ x ∷ t ++ l₃)
        p₀ = perm l₁ h x (t ++ l₃) refl

        p₁ : ((l₁ ++ [ h ]) ++ x ∷ t ++ l₃) ≋ ((l₁ ++ [ h ]) ++ t ++ x ∷ l₃)
        p₁ = ≋-del-ins-r (l₁ ++ [ h ]) x t l₃

        p₂ : (l₁ ++ [ h ]) ++ t ++ x ∷ l₃ ≡ l₁ ++ h ∷ t ++ x ∷ l₃
        p₂ = ∪-assoc l₁ [ h ] (t ++ x ∷ l₃)

        p₃ : (l₁ ++ [ h ]) ++ x ∷ t ++ l₃ ≡ l₁ ++ h ∷ x ∷ t ++ l₃
        p₃ = ∪-assoc l₁ [ h ] (x ∷ t ++ l₃)

        p₄ : ((l₁ ++ [ h ]) ++ x ∷ t ++ l₃) ≋ (l₁ ++ h ∷ t ++ x ∷ l₃)
        p₄ = ≡-elim′ (λ y → ((l₁ ++ [ h ]) ++ x ∷ t ++ l₃) ≋ y) p₂ p₁

        p₅ : (l₁ ++ h ∷ x ∷ t ++ l₃) ≋ (l₁ ++ h ∷ t ++ x ∷ l₃)
        p₅ = ≡-elim′ (λ y → y ≋ (l₁ ++ h ∷ t ++ x ∷ l₃)) p₃ p₄

≋-del-ins-l : ∀ {l} {A : Set l} (l₁ l₂ : List A) (x : A) (l₃ : List A) → (l₁ ++ l₂ ++ x ∷ l₃) ≋ (l₁ ++ x ∷ l₂ ++ l₃)
≋-del-ins-l l₁ l₂ x l₃ = ≋-sym $ ≋-del-ins-r l₁ x l₂ l₃

x∪[]≡x : ∀ {ℓ} {A : Set ℓ} (x : List A) → x ∪ [] ≡ x
x∪[]≡x [] = refl
x∪[]≡x (h ∷ t) = ≡-trans p₀ p₁
  where p₀ : (h ∷ t) ++ [] ≡ h ∷ t ++ []
        p₀ = ∪-assoc [ h ] t []
        p₁ : h ∷ t ++ [] ≡ h ∷ t
        p₁ = ≡-cong (λ x → h ∷ x) (x∪[]≡x t)

x∖[]≡x : (x : Names) → x ∖ [] ≡ x
x∖[]≡x [] = refl
x∖[]≡x (h ∷ t) = ≡-cong (_∷_ h) (x∖[]≡x t)

t∖[]≡t : ∀ {ℓ} {A : Set ℓ} (t : List (Named A)) → t ∖∖ [] ≡ t
t∖[]≡t [] = refl
t∖[]≡t (h ∷ t) = ≡-cong (_∷_ h) (t∖[]≡t t)

e∷x≋e∷y : ∀ {ℓ} {A : Set ℓ} (e : A) {x y : List A} → x ≋ y → e ∷ x ≋ e ∷ y
e∷x≋e∷y _ refl = refl
e∷x≋e∷y x (perm l₁ e₁ e₂ l₂ p) = perm (x ∷ l₁) e₁ e₂ l₂ (e∷x≋e∷y x p)

∪-sym : ∀ {ℓ} {A : Set ℓ} (x y : List A) → x ∪ y ≋ y ∪ x
∪-sym [] y = ≡-elim′ (λ z → y ≋ z) (≡-sym $ x∪[]≡x y) refl
∪-sym x [] = ≡-elim′ (λ z → z ≋ x) (≡-sym $ x∪[]≡x x) refl
∪-sym x (y ∷ ys) = ≡-elim′ (λ z → x ++ (y ∷ ys) ≋ z) p₃ (≋-trans p₁ p₂) where
    p₁ : x ++ (y ∷ ys) ≋ y ∷ (x ++ ys)
    p₁ = ≋-del-ins-l [] x y ys
    p₂ : y ∷ (x ++ ys) ≋ y ∷ (ys ++ x)
    p₂ = e∷x≋e∷y y $ ∪-sym x ys
    p₃ : y ∷ (ys ++ x) ≡ (y ∷ ys) ++ x
    p₃ = ∪-assoc [ y ] ys x

y≋ỳ⇒x∪y≋x∪ỳ : ∀ {ℓ} {A : Set ℓ} (x : List A) {y ỳ : List A} → y ≋ ỳ → x ∪ y ≋ x ∪ ỳ
y≋ỳ⇒x∪y≋x∪ỳ [] p = p
y≋ỳ⇒x∪y≋x∪ỳ (h ∷ t) p = e∷x≋e∷y h (y≋ỳ⇒x∪y≋x∪ỳ t p)

x≋x̀⇒x∪y≋x̀∪y : ∀ {ℓ} {A : Set ℓ} {x x̀ : List A} → x ≋ x̀ → (y : List A) → x ∪ y ≋ x̀ ∪ y
x≋x̀⇒x∪y≋x̀∪y {x = x} {x̀ = x̀} p y = ≋-trans (∪-sym x y) $ ≋-trans (y≋ỳ⇒x∪y≋x∪ỳ y p) (∪-sym y x̀)

x⊆y≋z : ∀ {ℓ} {A : Set ℓ} {x y z : List A} → x ⊆ y → y ≋ z → x ⊆ z
x⊆y≋z x⊆y refl = x⊆y
x⊆y≋z {x = x} {y = y} {z = .(l₁ ++ x₁ ∷ x₂ ∷ l₂)} x⊆y (perm l₁ x₁ x₂ l₂ p) = ∈-perm l₁ x₂ x₁ l₂ ∘ x⊆y≋z x⊆y p

x≋y⊆z : ∀ {ℓ} {A : Set ℓ} {x y z : List A} → x ≋ y → x ⊆ z → y ⊆ z
x≋y⊆z refl x⊆z = x⊆z
x≋y⊆z {y = .(l₁ ++ x₁ ∷ x₂ ∷ l₂)} {z = z} (perm l₁ x₁ x₂ l₂ p) x⊆z = x≋y⊆z p x⊆z ∘ ∈-perm l₁ x₁ x₂ l₂

x⊆x∪y : ∀ {ℓ} {A : Set ℓ} (x y : List A) → x ⊆ x ∪ y
x⊆x∪y .(x ∷ xs) y (here  {x} {xs} px) = here px
x⊆x∪y .(x ∷ xs) y (there {x} {xs} pxs) = there $ x⊆x∪y xs y pxs

x∪y⊆z⇒x⊆z : ∀ {ℓ} {A : Set ℓ} (x y : List A) {z : List A} → x ∪ y ⊆ z → x ⊆ z
x∪y⊆z⇒x⊆z x y x∪y⊆z = x∪y⊆z ∘ x⊆x∪y x y

x∪y⊆z⇒y⊆z : ∀ {ℓ} {A : Set ℓ} (x y : List A) {z : List A} → x ∪ y ⊆ z → y ⊆ z
x∪y⊆z⇒y⊆z x y = x∪y⊆z⇒x⊆z y x ∘ x≋y⊆z (∪-sym x y)

n-x∪y : ∀ {ℓ} {A : Set ℓ} (x y : List (Named A)) → names (x ∪ y) ≡ names x ∪ names y
n-x∪y [] _ = refl
n-x∪y {ℓ} (x ∷ xs) y = ≡-trans p₁ p₂ where
    nx = [ proj₁ x ]
    nxs = names xs
    ny = names y
    p₁ : nx ∪ names (xs ∪ y) ≡ nx ∪ (nxs ∪ ny)
    p₁ = ≡-cong (λ z → nx ∪ z) (n-x∪y xs y)
    p₂ : nx ∪ (nxs ∪ ny) ≡ (nx ∪ nxs) ∪ ny
    p₂ = ≡-sym $ ∪-assoc nx nxs ny

t-x∪y : ∀ {ℓ} (x y : Values ℓ) → types (x ∪ y) ≡ types x ∪ types y
t-x∪y [] _ = refl
t-x∪y (x ∷ xs) y = ≡-trans p₁ p₂ where
    nx = types [ x ]
    nxs = types xs
    ny = types y
    p₁ : nx ∪ types (xs ∪ y) ≡ nx ∪ (nxs ∪ ny)
    p₁ = ≡-cong (λ z → nx ∪ z) (t-x∪y xs y)
    p₂ : nx ∪ (nxs ∪ ny) ≡ (nx ∪ nxs) ∪ ny
    p₂ = ≡-sym $ ∪-assoc nx nxs ny

n-x≋y : ∀ {ℓ} {A : Set ℓ} {x y : List (Named A)} → x ≋ y → names x ≋ names y
n-x≋y refl = refl
n-x≋y (perm {x} l₁ e₁ e₂ l₂ p) = p₃ where
    n-l₁e₁e₂l₂ : ∀ e₁ e₂ → names (l₁ ++ e₁ ∷ e₂ ∷ l₂) ≡ names l₁ ++ names [ e₁ ] ++ names [ e₂ ] ++ names l₂
    n-l₁e₁e₂l₂ e₁ e₂ = ≡-trans p₁ $ ≡-trans p₂ p₃ where
        p₁ : names (l₁ ++ e₁ ∷ e₂ ∷ l₂) ≡ names l₁ ++ names (e₁ ∷ e₂ ∷ l₂)
        p₁ = n-x∪y l₁ (e₁ ∷ e₂ ∷ l₂)
        p₂ : names l₁ ++ names (e₁ ∷ e₂ ∷ l₂) ≡ names l₁ ++ names [ e₁ ] ++ names (e₂ ∷ l₂)
        p₂ = ≡-cong (λ z → names l₁ ++ z) (n-x∪y [ e₁ ] (e₂ ∷ l₂))
        p₃ : names l₁ ++ names [ e₁ ] ++ names (e₂ ∷ l₂) ≡ names l₁ ++ names [ e₁ ] ++ names [ e₂ ] ++ names l₂
        p₃ = ≡-cong (λ z → names l₁ ++ names [ e₁ ] ++ z) (n-x∪y [ e₂ ] l₂)

    p₁ : names x ≋ names l₁ ++ proj₁ e₂ ∷ proj₁ e₁ ∷ names l₂
    p₁ = ≡-elim′ (λ z → names x ≋ z) (n-l₁e₁e₂l₂ e₂ e₁) (n-x≋y p)
    p₂ : names x ≋ names l₁ ++ proj₁ e₁ ∷ proj₁ e₂ ∷ names l₂
    p₂ = perm (names l₁) (proj₁ e₁) (proj₁ e₂) (names l₂) p₁

    p₃ : names x ≋ names (l₁ ++ e₁ ∷ e₂ ∷ l₂)
    p₃ = ≡-elim′ (λ z → names x ≋ z) (≡-sym $ n-l₁e₁e₂l₂ e₁ e₂) p₂

n-types : ∀ {ℓ} (x : Values ℓ) → names (types x) ≡ names x
n-types [] = refl
n-types (x ∷ xs) = ≡-cong (λ z → proj₁ x ∷ z) (n-types xs)

nr-x≋y : ∀ {ℓ} {A : Set ℓ} {x y : List A} → x ≋ y → NonRepetitive x → NonRepetitive y
nr-x≋y refl u = u
nr-x≋y {y = .(l₁ ++ e₁ ∷ e₂ ∷ l₂)} (perm l₁ e₁ e₂ l₂ p) u = ≋-step l₁ e₂ e₁ l₂ (nr-x≋y p u) where
    ∉-step : ∀ {ℓ} {A : Set ℓ} {x : A} (l₁ : List A) (e₁ : A) (e₂ : A) (l₂ : List A) → x ∉ l₁ ++ e₁ ∷ e₂ ∷ l₂ → x ∉ l₁ ++ e₂ ∷ e₁ ∷ l₂
    ∉-step l₁ e₁ e₂ l₂ x∉l x∈l = ⊥-elim $ x∉l $ ∈-perm l₁ e₂ e₁ l₂ x∈l

    ≋-step : ∀ {ℓ} {A : Set ℓ} (l₁ : List A) (e₁ : A) (e₂ : A) (l₂ : List A) → NonRepetitive (l₁ ++ e₁ ∷ e₂ ∷ l₂) → NonRepetitive (l₁ ++ e₂ ∷ e₁ ∷ l₂)
    ≋-step [] e₁ e₂ l₂ (_∷_ .{e₁} .{e₂ ∷ l₂} e₁∉e₂∷l₂ (_∷_ .{e₂} .{l₂} e₂∉l₂ pU)) = e₂∉e₁∷l₂ ∷ e₁∉l₂ ∷ pU where
        e₁∉l₂ = e₁ ∉ l₂ ∋ x∉y∷l⇒x∉l e₁∉e₂∷l₂
        e₂∉e₁∷l₂ = e₂ ∉ e₁ ∷ l₂ ∋ x≢y⇒x∉l⇒x∉y∷l (≢-sym $ x∉y∷l⇒x≢y e₁∉e₂∷l₂) e₂∉l₂
    ≋-step (h₁ ∷ t₁) e₁ e₂ l₂ (_∷_ .{h₁} .{t₁ ++ e₁ ∷ e₂ ∷ l₂} p∉ pU) = ∉-step t₁ e₁ e₂ l₂ p∉ ∷ ≋-step t₁ e₁ e₂ l₂ pU

nr-x⇒nr-t-x : ∀ {ℓ} {x : Values ℓ} → NonRepetitiveNames x → NonRepetitiveNames (types x)
nr-x⇒nr-t-x {x = x} = ≡-elim′ NonRepetitive (≡-sym $ n-types x)

n-x∖y : ∀ {ℓ} {A : Set ℓ} (x : List (Named A)) (y : Names) → names (x ∖∖ y) ≡ names x ∖ y
n-x∖y [] _ = refl
n-x∖y (x ∷ xs) ny with not $ ny ∋! proj₁ x
... | false = n-x∖y xs ny
... | true = ≡-trans p₁ p₂ where
        p₁ : names (x ∷ (xs ∖∖ ny)) ≡ proj₁ x ∷ names (xs ∖∖ ny)
        p₁ = n-x∪y [ x ] (xs ∖∖ ny)
        p₂ : proj₁ x ∷ names (xs ∖∖ ny) ≡ proj₁ x ∷ (names xs ∖ ny)
        p₂ = ≡-cong (λ z → proj₁ x ∷ z) (n-x∖y xs ny)

t-x∖y : ∀ {ℓ} (x : Values ℓ) (y : Names) → types (x ∖∖ y) ≡ types x ∖∖ y
t-x∖y [] _ = refl
t-x∖y (x ∷ xs) ny with not $ ny ∋! proj₁ x
... | false = t-x∖y xs ny
... | true = ≡-trans p₁ p₂ where
        x̀ = types [ x ]
        p₁ : types (x ∷ (xs ∖∖ ny)) ≡ x̀ ∪ types (xs ∖∖ ny)
        p₁ = t-x∪y [ x ] (xs ∖∖ ny)
        p₂ : x̀ ∪ types (xs ∖∖ ny) ≡ x̀ ∪ (types xs ∖∖ ny)
        p₂ = ≡-cong (λ z → x̀ ∪ z) (t-x∖y xs ny)

n-filter-∈ : ∀ {ℓ} {A : Set ℓ} (x : List (Named A)) (y : Names) → names (filter-∈ x y) ≡ names x ∩ y
n-filter-∈ [] _ = refl
n-filter-∈ (x ∷ xs) ny with ny ∋! proj₁ x
... | false = n-filter-∈ xs ny
... | true = ≡-trans p₁ p₂ where
        p₁ : names (x ∷ (filter-∈ xs ny)) ≡ proj₁ x ∷ names (filter-∈ xs ny)
        p₁ = n-x∪y [ x ] (filter-∈ xs ny)
        p₂ : proj₁ x ∷ names (filter-∈ xs ny) ≡ proj₁ x ∷ (names xs ∩ ny)
        p₂ = ≡-cong (λ z → proj₁ x ∷ z) (n-filter-∈ xs ny)

t-filter-∈ : ∀ {ℓ} (x : Values ℓ) (y : Names) → types (filter-∈ x y) ≡ filter-∈ (types x) y
t-filter-∈ [] _ = refl
t-filter-∈ (x ∷ xs) ny with ny ∋! proj₁ x
... | false = t-filter-∈ xs ny
... | true = ≡-trans p₁ p₂ where
        x̀ = types [ x ]
        p₁ : types (x ∷ filter-∈ xs ny) ≡ x̀ ∪ types (filter-∈ xs ny)
        p₁ = t-x∪y [ x ] (filter-∈ xs ny)
        p₂ : x̀ ∪ types (filter-∈ xs ny) ≡ x̀ ∪ filter-∈ (types xs) ny
        p₂ = ≡-cong (λ z → x̀ ∪ z) (t-filter-∈ xs ny)

[]⊆x : ∀ {ℓ} {A : Set ℓ} (x : List A) → [] ⊆ x
[]⊆x _ ()

∀x∉[] : ∀ {ℓ} {A : Set ℓ} {x : A} → x ∉ []
∀x∉[] ()

x⊆[]⇒x≡[] : ∀ {ℓ} {A : Set ℓ} {x : List A} → x ⊆ [] → x ≡ []
x⊆[]⇒x≡[] {x = []} _ = refl
x⊆[]⇒x≡[] {x = _ ∷ _} x⊆[] = ⊥-elim $ ∀x∉[] $ x⊆[] (here refl)

x∩y⊆x : ∀ {ℓ} {A : Set ℓ} (x : List (Named A)) (y : Names) → filter-∈ x y ⊆ x
x∩y⊆x [] _ = λ()
x∩y⊆x (h ∷ t) y with y ∋! proj₁ h
... | false = there ∘ x∩y⊆x t y
... | true = f where
             f : h ∷ filter-∈ t y ⊆ h ∷ t
             f (here {x = .h} p) = here p
             f (there {xs = .(filter-∈ t y)} p) = there $ x∩y⊆x t y p

e∈x⇒e∈y∪x : ∀ {ℓ} {A : Set ℓ} {e : A} {x : List A} (y : List A) → e ∈ x → e ∈ y ∪ x
e∈x⇒e∈y∪x [] = id
e∈x⇒e∈y∪x (h ∷ t) = there ∘ e∈x⇒e∈y∪x t

e∈x⇒e∈x∪y : ∀ {ℓ} {A : Set ℓ} {e : A} {x : List A} (y : List A) → e ∈ x → e ∈ x ∪ y
e∈x⇒e∈x∪y {e = e} {x = x} y e∈x = x⊆y≋z f (∪-sym y x) (e ∈ [ e ] ∋ here refl) where
    f : [ e ] ⊆ y ∪ x
    f {è} (here {x = .e} p) = ≡-elim′ (λ z → z ∈ y ∪ x) (≡-sym p) (e∈x⇒e∈y∪x y e∈x)
    f (there ())

x∪y⊆x̀∪ỳ : ∀ {ℓ} {A : Set ℓ} {x x̀ y ỳ : List A} → x ⊆ x̀ → y ⊆ ỳ → x ∪ y ⊆ x̀ ∪ ỳ
x∪y⊆x̀∪ỳ {x = []} {x̀ = []} _ y⊆ỳ = y⊆ỳ
x∪y⊆x̀∪ỳ {x = []} {x̀ = _ ∷ t̀} _ y⊆ỳ = there ∘ x∪y⊆x̀∪ỳ ([]⊆x t̀) y⊆ỳ
x∪y⊆x̀∪ỳ {x = h ∷ t} {x̀ = x̀} {y = y} {ỳ = ỳ} x⊆x̀ y⊆ỳ = f where
    f : h ∷ t ∪ y ⊆ x̀ ∪ ỳ
    f {e} (here {x = .h} e≡h) = e∈x⇒e∈x∪y ỳ (x⊆x̀ $ here e≡h)
    f {e} (there {xs = .(t ∪ y)} p) = x∪y⊆x̀∪ỳ (x∪y⊆z⇒y⊆z [ h ] t x⊆x̀) y⊆ỳ p

x∖y⊆x : (x y : Names) → x ∖ y ⊆ x
x∖y⊆x [] _ = λ()
x∖y⊆x (h ∷ t) y with y ∋! h
... | true = there ∘ x∖y⊆x t y
... | false = x∪y⊆x̀∪ỳ (≋⇒⊆ $ ≡⇒≋ $ refl {x = [ h ]}) (x∖y⊆x t y)

t≋t∖n∪t∩n : ∀ {ℓ} {A : Set ℓ} (t : List (Named A)) (n : Names) → t ≋ (t ∖∖ n) ∪ filter-∈ t n
t≋t∖n∪t∩n [] _ = refl
t≋t∖n∪t∩n (h ∷ t) n with n ∋! proj₁ h
... | false = e∷x≋e∷y h $ t≋t∖n∪t∩n t n
... | true = ≋-trans p₁ p₂ where
           p₁ : h ∷ t ≋ h ∷ (t ∖∖ n) ∪ filter-∈ t n
           p₁ = e∷x≋e∷y h $ t≋t∖n∪t∩n t n
           p₂ : h ∷ (t ∖∖ n) ∪ filter-∈ t n ≋ (t ∖∖ n) ∪ h ∷ filter-∈ t n
           p₂ = ≋-del-ins-r [] h (t ∖∖ n) (filter-∈ t n)

e₁∈x⇒e₂∉x⇒e≢e₂ : ∀ {ℓ} {A : Set ℓ} {e₁ e₂ : A} {x : List A} → e₁ ∈ x → e₂ ∉ x → e₁ ≢ e₂
e₁∈x⇒e₂∉x⇒e≢e₂ e₁∈x e₂∉x refl = e₂∉x e₁∈x

e₁∈e₂∷x⇒e₁≢e₂⇒e₁∈x : ∀ {ℓ} {A : Set ℓ} {e₁ e₂ : A} {x : List A} → e₁ ∈ e₂ ∷ x → e₁ ≢ e₂ → e₁ ∈ x
e₁∈e₂∷x⇒e₁≢e₂⇒e₁∈x (here e₁≡e₂) e₁≢e₂ = ⊥-elim $ e₁≢e₂ e₁≡e₂
e₁∈e₂∷x⇒e₁≢e₂⇒e₁∈x (there e₁∈x) _ = e₁∈x

x⊆e∷y⇒e∉x⇒x⊆y : ∀ {ℓ} {A : Set ℓ} {e : A} {x y : List A} → x ⊆ e ∷ y → e ∉ x → x ⊆ y
x⊆e∷y⇒e∉x⇒x⊆y {e = e} {x = x} {y = y} x⊆e∷y e∉x {è} è∈x = e₁∈e₂∷x⇒e₁≢e₂⇒e₁∈x (x⊆e∷y è∈x) (e₁∈x⇒e₂∉x⇒e≢e₂ è∈x e∉x)

n-e∉l⇒e∉l : ∀ {ℓ} {A : Set ℓ} {e : Named A} {l : List (Named A)} → proj₁ e ∉ names l → e ∉ l
n-e∉l⇒e∉l {e = e} n-e∉l (here {x = è} p) = ⊥-elim $ n-e∉l $ here $ ≡-cong proj₁ p
n-e∉l⇒e∉l n-e∉l (there p) = n-e∉l⇒e∉l (x∉y∷l⇒x∉l n-e∉l) p

nr-names⇒nr : ∀ {ℓ} {A : Set ℓ} {l : List (Named A)} → NonRepetitiveNames l → NonRepetitive l
nr-names⇒nr {l = []} [] = []
nr-names⇒nr {l = _ ∷ _} (nh∉nt ∷ nr-t) = n-e∉l⇒e∉l nh∉nt ∷ nr-names⇒nr nr-t

e∉x⇒e∉y⇒e∉x∪y : ∀ {ℓ} {A : Set ℓ} {e : A} {x y : List A} → e ∉ x → e ∉ y → e ∉ x ∪ y
e∉x⇒e∉y⇒e∉x∪y {x = []} _  e∉y e∈y = ⊥-elim $ e∉y e∈y
e∉x⇒e∉y⇒e∉x∪y {x = h ∷ t} e∉x e∉y (here e≡h) = ⊥-elim $ e∉x $ here e≡h
e∉x⇒e∉y⇒e∉x∪y {x = h ∷ t} e∉x e∉y (there e∈t∪y) = e∉x⇒e∉y⇒e∉x∪y (x∉y∷l⇒x∉l e∉x) e∉y e∈t∪y

nr-x∖y∪y : {x y : Names} → NonRepetitive x → NonRepetitive y → NonRepetitive (x ∖ y ∪ y)
nr-x∖y∪y {x = []} _ nr-y = nr-y
nr-x∖y∪y {x = x ∷ xs} {y = y} (x∉xs ∷ nr-xs) nr-y with x ∈? y
... | yes x∈y = nr-x∖y∪y nr-xs nr-y
... | no x∉y = e∉x⇒e∉y⇒e∉x∪y (⊥-elim ∘ x∉xs ∘ x∖y⊆x xs y) x∉y ∷ nr-x∖y∪y nr-xs nr-y

e∉l∖[e] : (e : String) (l : Names) → e ∉ l ∖ [ e ]
e∉l∖[e] _ [] = λ()
e∉l∖[e] e (h ∷ t) with h ≟ e
... | yes _ = e∉l∖[e] e t
... | no h≢e = x≢y⇒x∉l⇒x∉y∷l (≢-sym h≢e) (e∉l∖[e] e t)

e∉l⇒l∖e≡l : {e : String} {l : Names} → e ∉ l → l ∖ [ e ] ≡ l
e∉l⇒l∖e≡l {e = e} {l = []} _ = refl
e∉l⇒l∖e≡l {e = e} {l = h ∷ t} e∉l with h ∈? [ e ]
... | yes h∈e = ⊥-elim $ x≢y⇒x∉l⇒x∉y∷l (≢-sym $ x∉y∷l⇒x≢y e∉l) (λ()) h∈e
... | no h∉e = ≡-cong (_∷_ h) (e∉l⇒l∖e≡l $ x∉y∷l⇒x∉l e∉l)

e∈l⇒nr-l⇒l∖e∪e≋l : {e : String} {l : Names} → e ∈ l → NonRepetitive l → l ∖ [ e ] ∪ [ e ] ≋ l
e∈l⇒nr-l⇒l∖e∪e≋l {l = []} () _
e∈l⇒nr-l⇒l∖e∪e≋l {e = e} {l = h ∷ t} e∈h∷t (h∉t ∷ nr-t) with h ∈? [ e ]
... | yes (here h≡e) = ≋-trans (≡⇒≋ $ ≡-trans p₁ p₂) (∪-sym t [ h ]) where
          p₁ : t ∖ [ e ] ∪ [ e ] ≡ t ∖ [ h ] ∪ [ h ]
          p₁ = ≡-cong (λ x → t ∖ [ x ] ∪ [ x ]) (≡-sym h≡e)
          p₂ : t ∖ [ h ] ∪ [ h ] ≡ t ∪ [ h ]
          p₂ = ≡-cong (λ x → x ∪ [ h ]) (e∉l⇒l∖e≡l h∉t)
... | yes (there ())
... | no  h∉e with e∈h∷t
...      | here e≡h = ⊥-elim ∘ h∉e ∘ here ∘ ≡-sym $ e≡h
...      | there e∈t = e∷x≋e∷y _ $ e∈l⇒nr-l⇒l∖e∪e≋l e∈t nr-t

nr-x∖y : {x : Names} → NonRepetitive x → (y : Names) → NonRepetitive (x ∖ y)
nr-x∖y {x = []} _ _ = []
nr-x∖y {x = x ∷ xs} (x∉xs ∷ nr-xs) y with x ∈? y
... | yes x∈y = nr-x∖y nr-xs y
... | no  x∉y = ⊥-elim ∘ x∉xs ∘ x∖y⊆x xs y ∷ nr-x∖y nr-xs y

x⊆y⇒e∉y⇒e∉x : ∀ {ℓ} {A : Set ℓ} {e : A} {x y : List A} → x ⊆ y → e ∉ y → e ∉ x
x⊆y⇒e∉y⇒e∉x x⊆y e∉y e∈x = e∉y $ x⊆y e∈x

e∈n-l⇒∃è,n-è≡e×è∈l : ∀ {ℓ} {A : Set ℓ} {e : String} {l : List (Named A)} → e ∈ names l → Σ[ è ∈ Named A ] e ≡ proj₁ è × è ∈ l
e∈n-l⇒∃è,n-è≡e×è∈l {l = []} ()
e∈n-l⇒∃è,n-è≡e×è∈l {l = h ∷ t} (here e≡n-h) = h , e≡n-h , here refl
e∈n-l⇒∃è,n-è≡e×è∈l {l = h ∷ t} (there e∈n-t) with e∈n-l⇒∃è,n-è≡e×è∈l e∈n-t
... | è , n-è≡e , è∈l = è , n-è≡e , there è∈l

x⊆y⇒nx⊆ny : ∀ {ℓ} {A : Set ℓ} {x y : List (Named A)} → x ⊆ y → names x ⊆ names y
x⊆y⇒nx⊆ny {x = x} {y = y} x⊆y {e} e∈n-x with e ∈? names y
... | yes e∈n-y = e∈n-y
... | no  e∉n-y with e∈n-l⇒∃è,n-è≡e×è∈l e∈n-x
...              | è , e≡n-è , è∈x = ⊥-elim $ x⊆y⇒e∉y⇒e∉x x⊆y (n-e∉l⇒e∉l $ ≡-elim′ (λ z → z ∉ names y) e≡n-è e∉n-y) è∈x

nr-x⇒nr-x∩y : ∀ {ℓ} {A : Set ℓ} {x : List (Named A)} → NonRepetitiveNames x → (y : Names) → NonRepetitiveNames (filter-∈ x y)
nr-x⇒nr-x∩y {x = []} _ _ = []
nr-x⇒nr-x∩y {x = h ∷ t} (h∉t ∷ nr-t) y with y ∋! proj₁ h
... | false = nr-x⇒nr-x∩y nr-t y
... | true = x⊆y⇒e∉y⇒e∉x (x⊆y⇒nx⊆ny $ x∩y⊆x t y) h∉t ∷ nr-x⇒nr-x∩y nr-t y

e∈l⇒[e]⊆l : ∀ {ℓ} {A : Set ℓ} {e : A} {l : List A} → e ∈ l → [ e ] ⊆ l
e∈l⇒[e]⊆l e∈l (here è≡e) = ≡-elim′ (λ x → x ∈ _) (≡-sym è≡e) e∈l
e∈l⇒[e]⊆l e∈l (there ())

a∈x⇒x≋y⇒a∈y : ∀ {ℓ} {A : Set ℓ} {x y : List A} {a : A} → a ∈ x → x ≋ y → a ∈ y
a∈x⇒x≋y⇒a∈y a∈x x≋y = x⊆y≋z (e∈l⇒[e]⊆l a∈x) x≋y (here refl)

x⊆z⇒y⊆z⇒x∪y⊆z : ∀ {ℓ} {A : Set ℓ} {x y z : List A} → x ⊆ z → y ⊆ z → x ∪ y ⊆ z
x⊆z⇒y⊆z⇒x∪y⊆z {x = []} _ y⊆z = y⊆z
x⊆z⇒y⊆z⇒x∪y⊆z {x = h ∷ t} {y = y} {z = z} x⊆z y⊆z = f where
    f : h ∷ t ∪ y ⊆ z
    f {e} (here e≡h) = x⊆z $ here e≡h
    f {e} (there e∈t∪y) = x⊆z⇒y⊆z⇒x∪y⊆z (x∪y⊆z⇒y⊆z [ h ] t x⊆z) y⊆z e∈t∪y

x⊆x∖y∪y : (x y : Names) → x ⊆ x ∖ y ∪ y
x⊆x∖y∪y [] _ = []⊆x _
x⊆x∖y∪y (h ∷ t) y with h ∈? y
x⊆x∖y∪y (h ∷ t) y | yes h∈y = x⊆z⇒y⊆z⇒x∪y⊆z (e∈l⇒[e]⊆l $ e∈x⇒e∈y∪x (t ∖ y) h∈y) (x⊆x∖y∪y t y)
x⊆x∖y∪y (h ∷ t) y | no _ = x∪y⊆x̀∪ỳ ([ h ] ⊆ [ h ] ∋ ≋⇒⊆ refl) (x⊆x∖y∪y t y)

e₁∈l⇒e₁∉l∖e₂⇒e₁≡e₂ : {e₁ e₂ : String} {l : Names} → e₁ ∈ l → e₁ ∉ l ∖ [ e₂ ] → e₁ ≡ e₂
e₁∈l⇒e₁∉l∖e₂⇒e₁≡e₂ {e₁ = e₁} {e₂ = e₂} {l = l} e₁∈l e₁∉l∖e₂ with e₁ ≟ e₂
... | yes e₁≡e₂ = e₁≡e₂
... | no e₁≢e₂ = ⊥-elim $ p₄ e₁∈l where
         p₁ : e₁ ∉ [ e₂ ] ∪ (l ∖ [ e₂ ])
         p₁ = x≢y⇒x∉l⇒x∉y∷l e₁≢e₂ e₁∉l∖e₂
         p₂ : [ e₂ ] ∪ (l ∖ [ e₂ ]) ≋ (l ∖ [ e₂ ]) ∪ [ e₂ ]
         p₂ = ∪-sym [ e₂ ] (l ∖ [ e₂ ])
         p₃ : e₁ ∉ (l ∖ [ e₂ ]) ∪ [ e₂ ]
         p₃ = p₁ ∘ ≋⇒⊆ (∪-sym (l ∖ [ e₂ ]) [ e₂ ])
         p₄ : e₁ ∉ l
         p₄ = x⊆y⇒e∉y⇒e∉x (x⊆x∖y∪y l [ e₂ ]) p₃

e∉x⇒x∩y≋x∩y∖e : {e : String} {x : Names} (y : Names) → e ∉ x → x ∩ y ≡ x ∩ (y ∖ [ e ])
e∉x⇒x∩y≋x∩y∖e {x = []} _ _ = refl
e∉x⇒x∩y≋x∩y∖e {e = e} {x = h ∷ t} y e∉x with h ∈? y | h ∈? (y ∖ [ e ])
... | yes h∈y | yes h∈y∖e = ≡-cong (_∷_ h) $ e∉x⇒x∩y≋x∩y∖e y $ x∉y∷l⇒x∉l e∉x
... | yes h∈y | no  h∉y∖e = ⊥-elim $ e∉x e∈x where
        e∈x : e ∈ h ∷ t
        e∈x = here $ ≡-sym $ e₁∈l⇒e₁∉l∖e₂⇒e₁≡e₂ h∈y h∉y∖e
... | no  h∉y | yes h∈y∖e = ⊥-elim $ h∉y $ x∖y⊆x y [ e ] h∈y∖e
... | no  h∉y | no  h∉y∖e = e∉x⇒x∩y≋x∩y∖e y $ x∉y∷l⇒x∉l e∉x

y⊆x⇒x∩y≋y : {x y : Names} → NonRepetitive y → NonRepetitive x → y ⊆ x → x ∩ y ≋ y
y⊆x⇒x∩y≋y {x = []} _ _ y⊆[] = ≡⇒≋ $ ≡-elim′ (λ y → [] ∩ y ≡ y) (≡-sym $ x⊆[]⇒x≡[] y⊆[]) refl
y⊆x⇒x∩y≋y {x = h ∷ t} {y = y} nr-y (h∉t ∷ nr-t) y⊆h∷t with h ∈? y
... | yes h∈y = ≋-trans (∪-sym [ h ] (t ∩ y)) p₄ where
        p₁ : t ∩ y ≋ t ∩ (y ∖ [ h ])
        p₁ = ≡⇒≋ $ e∉x⇒x∩y≋x∩y∖e y h∉t
        p₂ : t ∩ (y ∖ [ h ]) ≋ y ∖ [ h ]
        p₂ = y⊆x⇒x∩y≋y (nr-x∖y nr-y [ h ]) nr-t $ x⊆e∷y⇒e∉x⇒x⊆y (y⊆h∷t ∘ x∖y⊆x y [ h ]) (e∉l∖[e] h y)
        p₃ : y ∖ [ h ] ∪ [ h ] ≋ y
        p₃ = e∈l⇒nr-l⇒l∖e∪e≋l h∈y nr-y
        p₄ : t ∩ y ∪ [ h ] ≋ y
        p₄ = ≋-trans (x≋x̀⇒x∪y≋x̀∪y (≋-trans p₁ p₂) [ h ]) p₃
... | no  h∉y = y⊆x⇒x∩y≋y nr-y nr-t $ x⊆e∷y⇒e∉x⇒x⊆y y⊆h∷t h∉y

x∪y∖n≡x∖n∪y∖n : ∀ {ℓ} {A : Set ℓ} (x y : List (Named A)) (n : Names) → (x ∪ y) ∖∖ n ≡ (x ∖∖ n) ∪ (y ∖∖ n)
x∪y∖n≡x∖n∪y∖n [] _ _ = refl
x∪y∖n≡x∖n∪y∖n (h ∷ t) y n with proj₁ h ∈? n
... | yes _ = x∪y∖n≡x∖n∪y∖n t y n
... | no  _ = ≡-cong (_∷_ h) (x∪y∖n≡x∖n∪y∖n t y n)

n-x⊆n⇒x∖n≡[] : ∀ {ℓ} {A : Set ℓ} (x : List (Named A)) (n : Names) → names x ⊆ n → x ∖∖ n ≡ []
n-x⊆n⇒x∖n≡[] [] _ _ = refl
n-x⊆n⇒x∖n≡[] (h ∷ t) n n-x⊆n with proj₁ h ∈? n
... | yes _ = n-x⊆n⇒x∖n≡[] t n $ x∪y⊆z⇒y⊆z [ proj₁ h ] (names t) (x≋y⊆z (≡⇒≋ $ n-x∪y [ h ] t) n-x⊆n)
... | no h∉n = ⊥-elim $ h∉n $ n-x⊆n (proj₁ h ∈ proj₁ h ∷ names t ∋ here refl)

x∖x≡[] : ∀ {ℓ} {A : Set ℓ} (x : List (Named A)) → x ∖∖ names x ≡ []
x∖x≡[] x = n-x⊆n⇒x∖n≡[] x (names x) (≋⇒⊆ refl)

nr-[a] : ∀ {ℓ} {A : Set ℓ} {a : A} → NonRepetitive [ a ]
nr-[a] = (λ()) ∷ []

x≋y⇒x∖n≋y∖n : ∀ {ℓ} {A : Set ℓ} {x y : List (Named A)} → x ≋ y → (n : Names) → x ∖∖ n ≋ y ∖∖ n
x≋y⇒x∖n≋y∖n refl _ = refl
x≋y⇒x∖n≋y∖n {x = x} (perm l₁ x₁ x₂ l₂ p) n = ≋-trans p₀ $ ≋-trans (≡⇒≋ p₅) $ ≋-trans pg (≡⇒≋ $ ≡-sym g₅) where
    p₀ : x ∖∖ n ≋ (l₁ ++ x₂ ∷ x₁ ∷ l₂) ∖∖ n
    p₀ = x≋y⇒x∖n≋y∖n p n

    p₁ : (l₁ ++ [ x₂ ] ++ [ x₁ ] ++ l₂) ∖∖ n ≡ l₁ ∖∖ n ++ ([ x₂ ] ++ [ x₁ ] ++ l₂) ∖∖ n
    p₁ = x∪y∖n≡x∖n∪y∖n l₁ ([ x₂ ] ++ [ x₁ ] ++ l₂) n

    p₂ : l₁ ∖∖ n ++ ([ x₂ ] ++ [ x₁ ] ++ l₂) ∖∖ n ≡ l₁ ∖∖ n ++ [ x₂ ] ∖∖ n ++ ([ x₁ ] ++ l₂) ∖∖ n
    p₂ = ≡-cong (λ z → l₁ ∖∖ n ++ z) (x∪y∖n≡x∖n∪y∖n [ x₂ ] ([ x₁ ] ++ l₂) n)

    p₃ : l₁ ∖∖ n ++ [ x₂ ] ∖∖ n ++ ([ x₁ ] ++ l₂) ∖∖ n ≡ l₁ ∖∖ n ++ [ x₂ ] ∖∖ n ++ [ x₁ ] ∖∖ n ++ l₂ ∖∖ n
    p₃ = ≡-cong (λ z → l₁ ∖∖ n ++ [ x₂ ] ∖∖ n ++ z) (x∪y∖n≡x∖n∪y∖n [ x₁ ] l₂ n)

    p₄ : l₁ ∖∖ n ++ [ x₂ ] ∖∖ n ++ [ x₁ ] ∖∖ n ++ l₂ ∖∖ n ≡ l₁ ∖∖ n ++ ([ x₂ ] ∖∖ n ++ [ x₁ ] ∖∖ n) ++ l₂ ∖∖ n
    p₄ = ≡-cong (λ z → l₁ ∖∖ n ++ z) (≡-sym $ ∪-assoc ([ x₂ ] ∖∖ n) ([ x₁ ] ∖∖ n) (l₂ ∖∖ n))

    p₅ : (l₁ ++ [ x₂ ] ++ [ x₁ ] ++ l₂) ∖∖ n ≡ l₁ ∖∖ n ++ ([ x₂ ] ∖∖ n ++ [ x₁ ] ∖∖ n) ++ l₂ ∖∖ n
    p₅ = ≡-trans p₁ $ ≡-trans p₂ $ ≡-trans p₃ p₄

    pg : l₁ ∖∖ n ++ ([ x₂ ] ∖∖ n ++ [ x₁ ] ∖∖ n) ++ l₂ ∖∖ n ≋ l₁ ∖∖ n ++ ([ x₁ ] ∖∖ n ++ [ x₂ ] ∖∖ n) ++ l₂ ∖∖ n
    pg = y≋ỳ⇒x∪y≋x∪ỳ (l₁ ∖∖ n) $ x≋x̀⇒x∪y≋x̀∪y (∪-sym ([ x₂ ] ∖∖ n) ([ x₁ ] ∖∖ n)) (l₂ ∖∖ n)

    g₁ : (l₁ ++ [ x₁ ] ++ [ x₂ ] ++ l₂) ∖∖ n ≡ l₁ ∖∖ n ++ ([ x₁ ] ++ [ x₂ ] ++ l₂) ∖∖ n
    g₁ = x∪y∖n≡x∖n∪y∖n l₁ ([ x₁ ] ++ [ x₂ ] ++ l₂) n

    g₂ : l₁ ∖∖ n ++ ([ x₁ ] ++ [ x₂ ] ++ l₂) ∖∖ n ≡ l₁ ∖∖ n ++ [ x₁ ] ∖∖ n ++ ([ x₂ ] ++ l₂) ∖∖ n
    g₂ = ≡-cong (λ z → l₁ ∖∖ n ++ z) (x∪y∖n≡x∖n∪y∖n [ x₁ ] ([ x₂ ] ++ l₂) n)

    g₃ : l₁ ∖∖ n ++ [ x₁ ] ∖∖ n ++ ([ x₂ ] ++ l₂) ∖∖ n ≡ l₁ ∖∖ n ++ [ x₁ ] ∖∖ n ++ [ x₂ ] ∖∖ n ++ l₂ ∖∖ n
    g₃ = ≡-cong (λ z → l₁ ∖∖ n ++ [ x₁ ] ∖∖ n ++ z) (x∪y∖n≡x∖n∪y∖n [ x₂ ] l₂ n)

    g₄ : l₁ ∖∖ n ++ [ x₁ ] ∖∖ n ++ [ x₂ ] ∖∖ n ++ l₂ ∖∖ n ≡ l₁ ∖∖ n ++ ([ x₁ ] ∖∖ n ++ [ x₂ ] ∖∖ n) ++ l₂ ∖∖ n
    g₄ = ≡-cong (λ z → l₁ ∖∖ n ++ z) (≡-sym $ ∪-assoc ([ x₁ ] ∖∖ n) ([ x₂ ] ∖∖ n) (l₂ ∖∖ n))

    g₅ : (l₁ ++ [ x₁ ] ++ [ x₂ ] ++ l₂) ∖∖ n ≡ l₁ ∖∖ n ++ ([ x₁ ] ∖∖ n ++ [ x₂ ] ∖∖ n) ++ l₂ ∖∖ n
    g₅ = ≡-trans g₁ $ ≡-trans g₂ $ ≡-trans g₃ g₄

nr-x∪y⇒e∈x⇒e∈y⇒⊥ : ∀ {ℓ} {A : Set ℓ} {e : A} {x y : List A} → NonRepetitive (x ∪ y) → e ∈ x → e ∈ y → ⊥
nr-x∪y⇒e∈x⇒e∈y⇒⊥ {x = []} _ ()
nr-x∪y⇒e∈x⇒e∈y⇒⊥ {x = h ∷ t} (h∉t∪y ∷ nr-t∪y) (here e≡h) = h∉t∪y ∘ e∈x⇒e∈y∪x t ∘ ≡-elim′ (λ x → x ∈ _) e≡h
nr-x∪y⇒e∈x⇒e∈y⇒⊥ {x = h ∷ t} (h∉t∪y ∷ nr-t∪y) (there e∈t) = nr-x∪y⇒e∈x⇒e∈y⇒⊥ nr-t∪y e∈t

nr-x∪y⇒x∖y≡x : ∀ {ℓ} {A : Set ℓ} (x y : List (Named A)) → NonRepetitiveNames (x ∪ y) → y ∖∖ names x ≡ y
nr-x∪y⇒x∖y≡x x y nr-x∪y = f₀ y (≋⇒⊆ refl) where
    f₀ : ∀ t → t ⊆ y → t ∖∖ names x ≡ t
    f₀ [] _ = refl
    f₀ (h ∷ t) h∷t⊆y with proj₁ h ∈? names x
    ... | yes h∈x = ⊥-elim $ nr-x∪y⇒e∈x⇒e∈y⇒⊥ (≡-elim′ NonRepetitive (n-x∪y x y) nr-x∪y) h∈x (x⊆y⇒nx⊆ny h∷t⊆y $ here refl)
    ... | no _ = ≡-cong (_∷_ h) (f₀ t $ x∪y⊆z⇒y⊆z [ h ] t h∷t⊆y)

t≋t₁∪t₂⇒t∖t₁≋t₂ : ∀ {ℓ} {A : Set ℓ} {t : List (Named A)} → NonRepetitiveNames t → (t₁ t₂ : List (Named A)) → t ≋ t₁ ∪ t₂ → t ∖∖ names t₁ ≋ t₂
t≋t₁∪t₂⇒t∖t₁≋t₂ {t = t} nr-t t₁ t₂ t≋t₁∪t₂ = ≋-trans p₂ (≡⇒≋ $ nr-x∪y⇒x∖y≡x t₁ t₂ $ nr-x≋y (n-x≋y t≋t₁∪t₂) nr-t) where
    n-t₁ = names t₁
    p₁ : t ∖∖ n-t₁ ≋ (t₁ ∖∖ n-t₁) ∪ (t₂ ∖∖ n-t₁)
    p₁ = ≋-trans (x≋y⇒x∖n≋y∖n t≋t₁∪t₂ n-t₁) (≡⇒≋ $ x∪y∖n≡x∖n∪y∖n t₁ t₂ n-t₁)
    p₂ : t ∖∖ n-t₁ ≋ t₂ ∖∖ n-t₁
    p₂ = ≡-elim′ (λ x → t ∖∖ n-t₁ ≋ x ∪ (t₂ ∖∖ n-t₁)) (x∖x≡[] t₁) p₁

x≋x̀⇒y≋ỳ⇒x∪y≋x̀∪ỳ : ∀ {ℓ} {A : Set ℓ} {x x̀ y ỳ : List A} → x ≋ x̀ → y ≋ ỳ → x ∪ y ≋ x̀ ∪ ỳ
x≋x̀⇒y≋ỳ⇒x∪y≋x̀∪ỳ x≋x̀ (refl {y}) = x≋x̀⇒x∪y≋x̀∪y x≋x̀ y
x≋x̀⇒y≋ỳ⇒x∪y≋x̀∪ỳ {x = x} {x̀ = x̀} {y = y} {ỳ = ._} x≋x̀ (perm l₁ x₁ x₂ l₂ y≋l₁x₂x₁l₂) = ≋-trans p₁ $ ≋-trans p₂ $ ≋-trans p₃ p₄ where
    p₁ : x ∪ y ≋ x̀ ∪ (l₁ ++ x₂ ∷ x₁ ∷ l₂)
    p₁ = x≋x̀⇒y≋ỳ⇒x∪y≋x̀∪ỳ x≋x̀ y≋l₁x₂x₁l₂
    p₂ : x̀ ∪ (l₁ ++ x₂ ∷ x₁ ∷ l₂) ≋ (x̀ ∪ l₁) ++ x₂ ∷ x₁ ∷ l₂
    p₂ = ≡⇒≋ $ ≡-sym $ ∪-assoc x̀ l₁ (x₂ ∷ x₁ ∷ l₂)
    p₃ : (x̀ ∪ l₁) ++ x₂ ∷ x₁ ∷ l₂ ≋ (x̀ ∪ l₁) ++ x₁ ∷ x₂ ∷ l₂
    p₃ = perm (x̀ ∪ l₁) x₁ x₂ l₂ refl
    p₄ : (x̀ ∪ l₁) ++ x₁ ∷ x₂ ∷ l₂ ≋ x̀ ∪ (l₁ ++ x₁ ∷ x₂ ∷ l₂)
    p₄ = ≡⇒≋ $ ∪-assoc x̀ l₁ (x₁ ∷ x₂ ∷ l₂)

x∖y∪y≋y∖x∪x : ∀ {ℓ} {A : Set ℓ} (x y : List (Named A)) →
               let nx = names x
                   ny = names y
               in filter-∈ x ny ≋ filter-∈ y nx → x ∖∖ ny ∪ y ≋ y ∖∖ nx ∪ x
x∖y∪y≋y∖x∪x x y p₀ = ≋-trans p₁ $ ≋-trans p₂ p₃ where
    nx = names x
    ny = names y
    p₁ : x ∖∖ ny ∪ y ≋ x ∖∖ ny ∪ y ∖∖ nx ∪ filter-∈ y nx
    p₁ = ≋-trans (y≋ỳ⇒x∪y≋x∪ỳ (x ∖∖ ny) (t≋t∖n∪t∩n y nx)) (≡⇒≋ $ ≡-sym $ ∪-assoc (x ∖∖ ny) (y ∖∖ nx) (filter-∈ y nx))
    p₂ : (x ∖∖ ny ∪ y ∖∖ nx) ∪ filter-∈ y nx ≋ (y ∖∖ nx ∪ x ∖∖ ny) ∪ filter-∈ x ny
    p₂ = x≋x̀⇒y≋ỳ⇒x∪y≋x̀∪ỳ (∪-sym (x ∖∖ ny) (y ∖∖ nx)) (≋-sym p₀)
    p₃ : y ∖∖ nx ∪ x ∖∖ ny ∪ filter-∈ x ny ≋ y ∖∖ nx ∪ x
    p₃ = ≋-trans (≡⇒≋ $ ∪-assoc (y ∖∖ nx) (x ∖∖ ny) (filter-∈ x ny)) (≋-sym $ y≋ỳ⇒x∪y≋x∪ỳ (y ∖∖ nx) (t≋t∖n∪t∩n x ny))

names⇒named : Names → List (Named Unit)
names⇒named = mapL (λ x → x , unit)

nn-x∪y≡nn-x∪nn-y : ∀ x y → names⇒named (x ∪ y) ≡ names⇒named x ∪ names⇒named y
nn-x∪y≡nn-x∪nn-y [] y = refl
nn-x∪y≡nn-x∪nn-y (h ∷ t) y = ≡-cong (_∷_ _) (nn-x∪y≡nn-x∪nn-y t y)

nn-x≡x : ∀ x → names (names⇒named x) ≡ x
nn-x≡x [] = refl
nn-x≡x (h ∷ t) = ≡-cong (_∷_ h) (nn-x≡x t)

x≋y⇒nn-x≋nn-y : ∀ {x y} → x ≋ y → names⇒named x ≋ names⇒named y
x≋y⇒nn-x≋nn-y refl = refl
x≋y⇒nn-x≋nn-y {x = x} {y = ._} (perm l₁ x₁ x₂ l₂ x≋l₁x₂x₁l₂) = ≋-trans p₁ p₂ where
    p₁ : names⇒named x ≋ names⇒named l₁ ++ (x₂ , unit) ∷ (x₁ , unit) ∷ names⇒named l₂
    p₁ = ≋-trans (x≋y⇒nn-x≋nn-y x≋l₁x₂x₁l₂) (≡⇒≋ $ nn-x∪y≡nn-x∪nn-y l₁ (x₂ ∷ x₁ ∷ l₂))
    p₂ : names⇒named l₁ ++ (x₂ , unit) ∷ (x₁ , unit) ∷ names⇒named l₂ ≋ names⇒named (l₁ ++ x₁ ∷ x₂ ∷ l₂)
    p₂ = ≋-trans (perm (names⇒named l₁) (x₁ , unit) (x₂ , unit) (names⇒named l₂) refl) (≡⇒≋ $ ≡-sym $ nn-x∪y≡nn-x∪nn-y l₁ (x₁ ∷ x₂ ∷ l₂))

x≋y∪z⇒x∖y≋z : {x : Names} → NonRepetitive x → (y z : Names) → x ≋ y ∪ z → x ∖ y ≋ z
x≋y∪z⇒x∖y≋z {x} nr-x y z x≋y∪z = ≋-trans (≡⇒≋ $ ≡-sym $ ≡-trans p₂ p₃) (≋-trans p₁ $ ≡⇒≋ $ nn-x≡x z) where
    ux = names⇒named x
    uy = names⇒named y
    uz = names⇒named z
    ux≋uy∪uz : ux ≋ uy ∪ uz
    ux≋uy∪uz = ≋-trans (x≋y⇒nn-x≋nn-y x≋y∪z) (≡⇒≋ $ nn-x∪y≡nn-x∪nn-y y z)
    p₁ : names (ux ∖∖ names uy) ≋ names uz
    p₁ = n-x≋y $ t≋t₁∪t₂⇒t∖t₁≋t₂ (≡-elim′ NonRepetitive (≡-sym $ nn-x≡x x) nr-x) uy uz ux≋uy∪uz
    p₂ : names (ux ∖∖ names uy) ≡ names ux ∖ names uy
    p₂ = n-x∖y ux (names uy)
    p₃ : names ux ∖ names uy ≡ x ∖ y
    p₃ = ≡-cong₂ _∖_ (nn-x≡x x) (nn-x≡x y)

h∈x⇒∃t,x≋h∷t : ∀ {ℓ} {A : Set ℓ} {h : A} {x : List A} → h ∈ x → NonRepetitive x → Σ[ t ∈ List A ] x ≋ h ∷ t
h∈x⇒∃t,x≋h∷t {h = h} .{x = x ∷ xs} (here {x = x} {xs = xs} h≡x) (x∉xs ∷ nr-xs) = xs , ≡⇒≋ (≡-cong (λ z → z ∷ xs) (≡-sym h≡x))
h∈x⇒∃t,x≋h∷t {h = h} .{x = x ∷ xs} (there {x = x} {xs = xs} h∈xs) (x∉xs ∷ nr-xs) =
    let t , xs≋h∷t = ((Σ[ t ∈ List _ ] xs ≋ h ∷ t) ∋ h∈x⇒∃t,x≋h∷t h∈xs nr-xs)
        p₁ : x ∷ xs ≋ x ∷ h ∷ t
        p₁ = y≋ỳ⇒x∪y≋x∪ỳ [ x ] xs≋h∷t
        p₂ : x ∷ h ∷ t ≋ h ∷ x ∷ t
        p₂ = ≋-del-ins-l [] [ x ] h t
     in x ∷ t , ≋-trans p₁ p₂

nr-x∪y⇒nr-y : ∀ {ℓ} {A : Set ℓ} (x y : List A) → NonRepetitive (x ∪ y) → NonRepetitive y
nr-x∪y⇒nr-y [] _ nr-y = nr-y
nr-x∪y⇒nr-y (h ∷ t) y (_ ∷ nr-t∪y) = nr-x∪y⇒nr-y t y nr-t∪y

x⊆y⇒∃x̀,y≋x∪x̀ : ∀ {ℓ} {A : Set ℓ} {x y : List A} → NonRepetitive x → NonRepetitive y → x ⊆ y → Σ[ x̀ ∈ List A ] y ≋ x ∪ x̀
x⊆y⇒∃x̀,y≋x∪x̀ {x = []} {y = y} _ _ _ = y , refl
x⊆y⇒∃x̀,y≋x∪x̀ {x = h ∷ t} {y = y} (h∉t ∷ nr-t) nr-y h∷t⊆y =
    let ỳ , y≋h∷ỳ = h∈x⇒∃t,x≋h∷t (h∷t⊆y (h ∈ h ∷ t ∋ here refl)) nr-y
        p₁ : t ⊆ ỳ
        p₁ = x⊆e∷y⇒e∉x⇒x⊆y (x⊆y≋z (x∪y⊆z⇒y⊆z [ h ] t h∷t⊆y) y≋h∷ỳ) h∉t
        nr-ỳ = nr-x∪y⇒nr-y [ h ] ỳ $ nr-x≋y y≋h∷ỳ nr-y
        t̀ , ỳ≋t∪t̀ = x⊆y⇒∃x̀,y≋x∪x̀ nr-t nr-ỳ p₁
        p₂ : h ∷ ỳ ≋ h ∷ t ∪ t̀
        p₂ = y≋ỳ⇒x∪y≋x∪ỳ [ h ] ỳ≋t∪t̀
     in t̀ , ≋-trans y≋h∷ỳ p₂

t₁⊆t₂⇒t₂≋t₁∪t₂∖nt₁ : ∀ {ℓ} {A : Set ℓ} {t₁ t₂ : List (Named A)} → NonRepetitiveNames t₁ → NonRepetitiveNames t₂ → t₁ ⊆ t₂ → t₂ ≋ t₁ ∪ t₂ ∖∖ names t₁
t₁⊆t₂⇒t₂≋t₁∪t₂∖nt₁ {t₁ = t₁} {t₂ = t₂} nr-nt₁ nr-nt₂ t₁⊆t₂ = ≋-trans p₁ $ y≋ỳ⇒x∪y≋x∪ỳ t₁ p₆ where
    n-t₁ = names t₁
    nr-t₁ = nr-names⇒nr nr-nt₁
    nr-t₂ = nr-names⇒nr nr-nt₂
    t̀₁,t₁∪t̀₁≋t₂ = x⊆y⇒∃x̀,y≋x∪x̀ nr-t₁ nr-t₂ t₁⊆t₂
    t̀₁ = proj₁ t̀₁,t₁∪t̀₁≋t₂
    p₁ : t₂ ≋ t₁ ∪ t̀₁
    p₁ = proj₂ t̀₁,t₁∪t̀₁≋t₂
    p₂ : t₂ ∖∖ n-t₁ ≋ (t₁ ∪ t̀₁) ∖∖ n-t₁
    p₂ = x≋y⇒x∖n≋y∖n p₁ n-t₁
    p₃ : (t₁ ∪ t̀₁) ∖∖ n-t₁ ≡ t₁ ∖∖ n-t₁ ∪ t̀₁ ∖∖ n-t₁
    p₃ = x∪y∖n≡x∖n∪y∖n t₁ t̀₁ n-t₁
    p₄ : t₁ ∖∖ n-t₁ ∪ t̀₁ ∖∖ n-t₁ ≡ t̀₁ ∖∖ n-t₁
    p₄ = ≡-cong (λ x → x ∪ t̀₁ ∖∖ n-t₁) (x∖x≡[] t₁)
    p₅ : t̀₁ ∖∖ n-t₁ ≡ t̀₁
    p₅ = nr-x∪y⇒x∖y≡x t₁ t̀₁ $ nr-x≋y (n-x≋y p₁) nr-nt₂
    p₆ : t̀₁ ≋ t₂ ∖∖ n-t₁
    p₆ = ≋-sym $ ≋-trans p₂ $ ≡⇒≋ $ ≡-trans p₃ $ ≡-trans p₄ p₅

t₁⊆t₂⇒t₁≋f∈-t₂-nt₁ : ∀ {ℓ} {A : Set ℓ} {t₁ t₂ : List (Named A)} → NonRepetitiveNames t₁ → NonRepetitiveNames t₂ → t₁ ⊆ t₂ → t₁ ≋ filter-∈ t₂ (names t₁)
t₁⊆t₂⇒t₁≋f∈-t₂-nt₁ {t₁ = t₁} {t₂ = t₂} nr-t₁ nr-t₂ t₁⊆t₂ = ≋-trans (≋-sym p₃) p₄ where
    nt₁ = names t₁
    p₁ : t₂ ≋ t₂ ∖∖ nt₁ ∪ t₁
    p₁ = ≋-trans (t₁⊆t₂⇒t₂≋t₁∪t₂∖nt₁ nr-t₁ nr-t₂ t₁⊆t₂) (∪-sym t₁ (t₂ ∖∖ nt₁))
    p₂ : t₂ ≋ t₂ ∖∖ nt₁ ∪ filter-∈ t₂ nt₁
    p₂ = t≋t∖n∪t∩n t₂ nt₁
    p₃ : t₂ ∖∖ names (t₂ ∖∖ nt₁) ≋ t₁
    p₃ = t≋t₁∪t₂⇒t∖t₁≋t₂ nr-t₂ (t₂ ∖∖ nt₁) t₁ p₁
    p₄ : t₂ ∖∖ names (t₂ ∖∖ nt₁) ≋ filter-∈ t₂ nt₁
    p₄ = t≋t₁∪t₂⇒t∖t₁≋t₂ nr-t₂ (t₂ ∖∖ nt₁) (filter-∈ t₂ nt₁) p₂

-- /lemmas

-- assertions

infix 4 _s-≢!_
_s-≢!_ : String → String → Set
x s-≢! y with x ≟ y
... | yes _ = ⊥
... | no  _ = ⊤

s-≢!⇒≢? : ∀ {x y} → x s-≢! y → x ≢ y
s-≢!⇒≢? {x} {y} x≢!y with x ≟ y
s-≢!⇒≢? () | yes _
s-≢!⇒≢? _  | no p = p

s-NonRepetitive? : (n : Names) → Dec (NonRepetitive n)
s-NonRepetitive? [] = yes []
s-NonRepetitive? (h ∷ t) with h ∈? t | s-NonRepetitive? t
... | no h∉t | yes nr-t = yes (h∉t ∷ nr-t)
... | yes h∈t | _ = no f where
                    f : NonRepetitive (_ ∷ _) → _
                    f (h∉t ∷ _) = h∉t h∈t
... | _ | no ¬nr-t = no f where
                    f : NonRepetitive (_ ∷ _) → _
                    f (_ ∷ nr-t) = ¬nr-t nr-t

s-NonRepetitive! : Names → Set
s-NonRepetitive! n with s-NonRepetitive? n
... | yes _ = ⊤
... | no _ = ⊥

NonRepetitiveNames! : ∀ {ℓ} {A : Set ℓ} → List (Named A) → Set
NonRepetitiveNames! = s-NonRepetitive! ∘ names

s-nr!⇒nr : {n : Names} → s-NonRepetitive! n → NonRepetitive n
s-nr!⇒nr {n = n} _ with s-NonRepetitive? n
s-nr!⇒nr _ | yes p = p
s-nr!⇒nr () | no _

-- /assertions
