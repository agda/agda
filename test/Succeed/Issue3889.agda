-- Andreas, 2019-07-05, during work on issue #3889
-- Test-case for with extracted from the standard library

{-# OPTIONS --cubical-compatible #-}

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.List

open import Common.Equality
open import Common.Product

data Any {a}{A : Set a} {p} (P : A → Set p) : List A → Set (a ⊔ p) where
  here  : ∀ {x xs} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)

_∈_ : ∀{a}{A : Set a} → A → List A → Set _
x ∈ xs = Any (x ≡_) xs

map : ∀ {a} {A : Set a} {p q} {P : A → Set p} {Q : A → Set q} → (∀{x} → P x → Q x) → ∀{xs} → Any P xs → Any Q xs
map g (here px)   = here (g px)
map g (there pxs) = there (map g pxs)

map₁ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
       (A → B) → A × C → B × C
map₁ f (x ,  y)= f x , y

map₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c} →
       (∀ {x} → B x → C x) → Σ A B → Σ A C
map₂ f (x , y) = (x , f y)

find : ∀ {a} {p} {A : Set a} {P : A → Set p} {xs} → Any P xs → Σ _ λ x → x ∈ xs × P x
find (here px)   = (_ , here refl , px)
find (there pxs) = map₂ (map₁ there) (find pxs)

lose : ∀ {a} {p} {A : Set a} {P : A → Set p} {x xs} → x ∈ xs → P x → Any P xs
lose x∈xs px = map (λ eq → subst _ eq px) x∈xs

map∘find : ∀ {a p} {A : Set a} {P : A → Set p} {xs}
           (p : Any P xs) → let p′ = find p in
           {f : ∀{x} → proj₁ p′ ≡ x → P x} →
           f refl ≡ proj₂ (proj₂ p′) →
           map f (proj₁ (proj₂ p′)) ≡ p
map∘find (here  p) hyp = cong here  hyp
map∘find (there p) hyp = cong there (map∘find p hyp)

find∘map : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
           {xs : List A} (p : Any P xs) (f : ∀{x} → P x → Q x) →
           find (map f p) ≡ map₂ (map₂ f) (find p)
find∘map (here  p) f = refl
find∘map (there p) f rewrite find∘map p f = refl

lose∘find : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A}
            (p : Any P xs) →
            (let (y , z) = proj₂ (find p)) →
            lose y z ≡ p
lose∘find p = map∘find p refl

postulate
  a b ℓ : Level
  A : Set a
  B : Set b
  P : A → Set ℓ
  Q : B → Set ℓ   -- Level needed

Any-×⁺ : ∀ {xs ys} → Any P xs × Any Q ys →
         Any (λ x → Any (λ y → P x × Q y) ys) xs
Any-×⁺ (p , q) = map (λ p → map (λ q → (p , q)) q) p

Any-×⁻ : ∀ {xs ys} → Any (λ x → Any (λ y → P x × Q y) ys) xs →
         Any P xs × Any Q ys
Any-×⁻ pq with map₂ (map₂ find) (find pq)
... | (x , x∈xs , y , y∈ys , p , q) = (lose x∈xs p , lose y∈ys q)

module _ where
  from∘to : ∀{xs ys} (pq : Any P xs × Any Q ys) → Any-×⁻ (Any-×⁺ pq) ≡ pq
  -- from∘to (p , q) = {!!}
  from∘to (p , q) rewrite
      find∘map p (λ p → map (λ q → (p , q)) q)
    | find∘map q (λ q → proj₂ (proj₂ (find p)) , q)
    | lose∘find p
    | lose∘find q
    = refl
