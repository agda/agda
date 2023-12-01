data _＝_ {X : Set} : X → X → Set where
 refl : {x : X} → x ＝ x

record Σ {X : Set} (Y : X → Set) : Set  where
 constructor
  _,_
 field
  pr₁ : X
  pr₂ : Y pr₁

_×_ : Set → Set → Set
X × Y = Σ λ (_ : X) → Y

id : {X : Set} → X → X
id x = x

_∘_ : {X : Set} {Y : Set} {Z : Y → Set}
    → ((y : Y) → Z y)
    → (f : X → Y) (x : X) → Z (f x)
g ∘ f = λ x → g (f x)

_∼_ : {X : Set} {A : X → Set} → ((x : X) → A x) → ((x : X) → A x) → Set
f ∼ g = ∀ x → f x ＝ g x

_≅_ : Set → Set → Set
X ≅ Y = Σ λ (f : X → Y) → Σ λ (g : Y → X) → (g ∘ f ∼ id) × (f ∘ g ∼ id)

fact : (X Y : Set) (A : X → Set) (B : Y → Set) →
       (Σ λ (x : X) → Σ λ (y : Y) → A x × B y)
     ≅ ((Σ λ (x : X) → A x) × (Σ λ (y : Y) → B y))
fact X Y A B = f , g , gf , fg
  where
   f : _
   f (x , y , a , b) = ((x , a) , (y , b))
   g : _
   g ((x , a) , (y , b)) = x , y , a , b
   fg : f ∘ g ∼ id
   fg _ = refl
   gf : g ∘ f ∼ id
   gf _ = refl

infixr 50 _,_
infixl 5 _∘_
infix  4 _∼_
infixr 2 _×_
