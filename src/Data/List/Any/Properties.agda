------------------------------------------------------------------------
-- Properties relating Any to various list functions
------------------------------------------------------------------------

module Data.List.Any.Properties where

open import Category.Monad
open import Data.Bool
open import Data.Bool.Properties
open import Data.Function
open import Data.List as List
open RawMonad List.monad
open import Data.List.Any as Any using (Any; here; there)
import Data.List.Equality as ListEq
open import Data.Product as Prod hiding (map)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Unary using (Pred; _⟨×⟩_; _⟨→⟩_)
open import Relation.Binary
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.FunctionSetoid
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; inspect; _with-≡_)

------------------------------------------------------------------------
-- Lemmas related to Any

-- Introduction (⁺) and elimination (⁻) rules for map.

map⁺ : ∀ {A B} {P : Pred B} {f : A → B} {xs} →
       Any (P ∘₀ f) xs → Any P (map f xs)
map⁺ (here p)  = here p
map⁺ (there p) = there $ map⁺ p

map⁻ : ∀ {A B} {P : Pred B} {f : A → B} {xs} →
       Any P (map f xs) → Any (P ∘₀ f) xs
map⁻ {xs = []}     ()
map⁻ {xs = x ∷ xs} (here p)  = here p
map⁻ {xs = x ∷ xs} (there p) = there $ map⁻ p

-- Introduction and elimination rules for _++_.

++⁺ˡ : ∀ {A} {P : Pred A} {xs ys} →
       Any P xs → Any P (xs ++ ys)
++⁺ˡ (here p)  = here p
++⁺ˡ (there p) = there (++⁺ˡ p)

++⁺ʳ : ∀ {A} {P : Pred A} xs {ys} →
       Any P ys → Any P (xs ++ ys)
++⁺ʳ []       p = p
++⁺ʳ (x ∷ xs) p = there (++⁺ʳ xs p)

++⁻ : ∀ {A} {P : Pred A} xs {ys} →
      Any P (xs ++ ys) → Any P xs ⊎ Any P ys
++⁻ []       p         = inj₂ p
++⁻ (x ∷ xs) (here p)  = inj₁ (here p)
++⁻ (x ∷ xs) (there p) = Sum.map there id (++⁻ xs p)

-- Introduction and elimination rules for return.

return⁺ : ∀ {A} {P : Pred A} {x} →
          P x → Any P (return x)
return⁺ = here

return⁻ : ∀ {A} {P : Pred A} {x} →
          Any P (return x) → P x
return⁻ (here p)   = p
return⁻ (there ())

-- Introduction and elimination rules for concat.

concat⁺ : ∀ {A} {P : Pred A} {xss} →
          Any (Any P) xss → Any P (concat xss)
concat⁺ (here p)           = ++⁺ˡ p
concat⁺ (there {x = xs} p) = ++⁺ʳ xs (concat⁺ p)

concat⁻ : ∀ {A} {P : Pred A} xss →
          Any P (concat xss) → Any (Any P) xss
concat⁻ []               ()
concat⁻ ([]       ∷ xss) p         = there $ concat⁻ xss p
concat⁻ ((x ∷ xs) ∷ xss) (here p)  = here (here p)
concat⁻ ((x ∷ xs) ∷ xss) (there p)
  with concat⁻ (xs ∷ xss) p
... | here  p′ = here (there p′)
... | there p′ = there p′

-- Introduction and elimination rules for _>>=_.

>>=⁺ : ∀ {A B P xs} {f : A → List B} →
       Any (Any P ∘₀ f) xs → Any P (xs >>= f)
>>=⁺ = concat⁺ ∘ map⁺

>>=⁻ : ∀ {A B P} xs {f : A → List B} →
       Any P (xs >>= f) → Any (Any P ∘₀ f) xs
>>=⁻ _ = map⁻ ∘ concat⁻ _

-- Introduction and elimination rules for _⊛_.

⊛⁺ : ∀ {A B P} {fs : List (A → B)} {xs} →
     Any (λ f → Any (P ∘₀ f) xs) fs → Any P (fs ⊛ xs)
⊛⁺ = >>=⁺ ∘ Any.map (>>=⁺ ∘ Any.map return⁺)

⊛⁺′ : ∀ {A B P Q} {fs : List (A → B)} {xs} →
      Any (P ⟨→⟩ Q) fs → Any P xs → Any Q (fs ⊛ xs)
⊛⁺′ pq p = ⊛⁺ (Any.map (λ pq → Any.map (λ {x} → pq {x}) p) pq)

⊛⁻ : ∀ {A B P} (fs : List (A → B)) xs →
     Any P (fs ⊛ xs) → Any (λ f → Any (P ∘₀ f) xs) fs
⊛⁻ fs xs = Any.map (Any.map return⁻ ∘ >>=⁻ xs) ∘ >>=⁻ fs

-- Introduction and elimination rules for _⊗_.

⊗⁺ : ∀ {A B P} {xs : List A} {ys : List B} →
     Any (λ x → Any (λ y → P (x , y)) ys) xs → Any P (xs ⊗ ys)
⊗⁺ = ⊛⁺ ∘′ ⊛⁺ ∘′ return⁺

⊗⁺′ : ∀ {A B} {P : Pred A} {Q : Pred B} {xs ys} →
      Any P xs → Any Q ys → Any (P ⟨×⟩ Q) (xs ⊗ ys)
⊗⁺′ p q = ⊗⁺ (Any.map (λ p → Any.map (λ q → (p , q)) q) p)

⊗⁻ : ∀ {A B P} (xs : List A) (ys : List B) →
     Any P (xs ⊗ ys) → Any (λ x → Any (λ y → P (x , y)) ys) xs
⊗⁻ _ _ = return⁻ ∘ ⊛⁻ _ _ ∘ ⊛⁻ _ _

⊗⁻′ : ∀ {A B} {P : Pred A} {Q : Pred B} xs ys →
      Any (P ⟨×⟩ Q) (xs ⊗ ys) → Any P xs × Any Q ys
⊗⁻′ _ _ pq =
  (Any.map (proj₁ ∘ proj₂ ∘ Any.satisfied) lem ,
   (Any.map proj₂ $ proj₂ (Any.satisfied lem)))
  where lem = ⊗⁻ _ _ pq

-- Any and any are related via T.

any⁺ : ∀ {A} (p : A → Bool) {xs} →
       Any (T ∘₀ p) xs → T (any p xs)
any⁺ p (here  px)          = proj₂ T-∨ (inj₁ px)
any⁺ p (there {x = x} pxs) with p x
... | true  = _
... | false = any⁺ p pxs

any⁻ : ∀ {A} (p : A → Bool) xs →
       T (any p xs) → Any (T ∘₀ p) xs
any⁻ p []       ()
any⁻ p (x ∷ xs) px∷xs with inspect (p x)
any⁻ p (x ∷ xs) px∷xs | true  with-≡ eq = here (proj₂ T-≡ $
                                                  PropEq.sym eq)
any⁻ p (x ∷ xs) px∷xs | false with-≡ eq with p x
any⁻ p (x ∷ xs) pxs   | false with-≡ refl | .false =
  there (any⁻ p xs pxs)

------------------------------------------------------------------------
-- Lemmas related to _∈_, parameterised on underlying equalities

module Membership₁ (S : Setoid) where

  open Any.Membership S
  private
    open module S = Setoid S using (_≈_)
    open module [M] = Any.Membership (ListEq.Equality.setoid S)
      using () renaming (_∈_ to _[∈]_; _⊆_ to _[⊆]_)
    open module M≡ = Any.Membership-≡
      using () renaming (_∈_ to _∈≡_; _⊆_ to _⊆≡_)

  -- Any is monotone.

  mono : ∀ {P xs ys} →
         P Respects _≈_ → xs ⊆ ys → Any P xs → Any P ys
  mono resp xs⊆ys pxs with find pxs
  ... | (x , x∈xs , px) = lose resp (xs⊆ys x∈xs) px

  -- _++_ is monotone.

  _++-mono_ : ∀ {xs₁ xs₂ ys₁ ys₂} →
              xs₁ ⊆ ys₁ → xs₂ ⊆ ys₂ → xs₁ ++ xs₂ ⊆ ys₁ ++ ys₂
  _++-mono_ {ys₁ = ys₁} xs₁⊆ys₁ xs₂⊆ys₂ =
    [ ++⁺ˡ ∘ xs₁⊆ys₁ , ++⁺ʳ ys₁ ∘ xs₂⊆ys₂ ]′ ∘ ++⁻ _

  -- _++_ is idempotent.

  ++-idempotent : ∀ {xs} → xs ++ xs ⊆ xs
  ++-idempotent = [ id , id ]′ ∘ ++⁻ _

  -- Introduction and elimination rules for concat.

  concat-∈⁺ : ∀ {x xs xss} →
              x ∈ xs → xs [∈] xss → x ∈ concat xss
  concat-∈⁺ x∈xs xs∈xss =
    concat⁺ (Any.map (λ xs≈ys → P.reflexive xs≈ys x∈xs) xs∈xss)
    where module P = Preorder ⊆-preorder

  concat-∈⁻ : ∀ {x} xss → x ∈ concat xss →
              ∃ λ xs → x ∈ xs × xs [∈] xss
  concat-∈⁻ xss x∈ = Prod.map id swap $ [M].find (concat⁻ xss x∈)

  -- concat is monotone.

  concat-mono : ∀ {xss yss} →
                xss [⊆] yss → concat xss ⊆ concat yss
  concat-mono {xss = xss} xss⊆yss x∈ with concat-∈⁻ xss x∈
  ... | (xs , x∈xs , xs∈xss) = concat-∈⁺ x∈xs (xss⊆yss xs∈xss)

  -- any is monotone.

  any-mono : ∀ p → (T ∘₀ p) Respects _≈_ →
             ∀ {xs ys} → xs ⊆ ys → T (any p xs) → T (any p ys)
  any-mono p resp xs⊆ys = any⁺ p ∘ mono resp xs⊆ys ∘ any⁻ p _

  -- Introduction and elimination rules for map-with-∈.

  map-with-∈-∈⁺ : ∀ {A} {xs : List A}
                  (f : ∀ {x} → x ∈≡ xs → S.carrier) {x} →
                  (x∈xs : x ∈≡ xs) → f x∈xs ∈ M≡.map-with-∈ xs f
  map-with-∈-∈⁺ f (here refl)  = here S.refl
  map-with-∈-∈⁺ f (there x∈xs) = there $ map-with-∈-∈⁺ (f ∘ there) x∈xs

  map-with-∈-∈⁻ : ∀ {A} {xs : List A}
                  (f : ∀ {x} → x ∈≡ xs → S.carrier) {fx∈xs} →
                  fx∈xs ∈ M≡.map-with-∈ xs f →
                  ∃ λ x → Σ (x ∈≡ xs) λ x∈xs → fx∈xs ≈ f x∈xs
  map-with-∈-∈⁻ {xs = []}     f ()
  map-with-∈-∈⁻ {xs = y ∷ xs} f (here fx≈)   = (y , here refl , fx≈)
  map-with-∈-∈⁻ {xs = y ∷ xs} f (there x∈xs) =
    Prod.map id (Prod.map there id) $ map-with-∈-∈⁻ (f ∘ there) x∈xs

  -- map-with-∈ is monotone.

  map-with-∈-mono :
    ∀ {A} {xs : List A} {f : ∀ {x} → x ∈≡ xs → S.carrier}
          {ys : List A} {g : ∀ {x} → x ∈≡ ys → S.carrier} →
    (xs⊆ys : xs ⊆≡ ys) →
    (∀ {x} (x∈xs : x ∈≡ xs) → f x∈xs ≈ g (xs⊆ys x∈xs)) →
    M≡.map-with-∈ xs f ⊆ M≡.map-with-∈ ys g
  map-with-∈-mono {f = f} {g = g} xs⊆ys f≈g {fx∈xs} fx∈xs∈
    with map-with-∈-∈⁻ f fx∈xs∈
  ... | (x , x∈xs , fx∈xs≈) =
    Any.map (λ {y} g[xs⊆ys-x∈xs]≈y → begin
               fx∈xs           ≈⟨ fx∈xs≈ ⟩
               f x∈xs          ≈⟨ f≈g x∈xs ⟩
               g (xs⊆ys x∈xs)  ≈⟨ g[xs⊆ys-x∈xs]≈y ⟩
               y               ∎) $
            map-with-∈-∈⁺ g (xs⊆ys x∈xs)
    where open EqReasoning S

module Membership₂ (S₁ S₂ : Setoid) where

  private
    open module S₁ = Setoid S₁ using () renaming (_≈_ to _≈₁_)
    open module S₂ = Setoid S₂ using () renaming (_≈_ to _≈₂_)
    module L₂      = ListEq.Equality S₂
    open module M₁ = Any.Membership S₁
      using () renaming (_∈_ to _∈₁_; _⊆_ to _⊆₁_)
    open module M₂ = Any.Membership S₂
      using () renaming (_∈_ to _∈₂_; _⊆_ to _⊆₂_)
    open module M₁₂ = Any.Membership (S₁ ⇨ S₂)
      using () renaming (_∈_ to _∈₁₂_; _⊆_ to _⊆₁₂_)
    open Any.Membership (S₁ ×-setoid S₂)
      using () renaming (_⊆_ to _⊆₁,₂_)

  -- Introduction and elimination rules for map.

  map-∈⁺ : ∀ (f : S₁ ⟶ S₂) {x xs} →
          x ∈₁ xs → f ⟨$⟩ x ∈₂ map (_⟨$⟩_ f) xs
  map-∈⁺ f = map⁺ ∘ Any.map (pres f)

  map-∈⁻ : ∀ {f fx} xs →
           fx ∈₂ map f xs → ∃ λ x → x ∈₁ xs × fx ≈₂ f x
  map-∈⁻ _ fx∈ = M₁.find (map⁻ fx∈)

  -- map is monotone.

  map-mono : ∀ (f : S₁ ⟶ S₂) {xs ys} →
             xs ⊆₁ ys → map (_⟨$⟩_ f) xs ⊆₂ map (_⟨$⟩_ f) ys
  map-mono f xs⊆ys fx∈ with map-∈⁻ _ fx∈
  ... | (x , x∈ , eq) = Any.map (S₂.trans eq) (map-∈⁺ f (xs⊆ys x∈))

  -- Introduction and elimination rules for _>>=_.

  >>=-∈⁺ : ∀ (f : S₁ ⟶ L₂.setoid) {x y xs} →
           x ∈₁ xs → y ∈₂ f ⟨$⟩ x → y ∈₂ (xs >>= _⟨$⟩_ f)
  >>=-∈⁺ f x∈xs y∈fx =
    >>=⁺ (Any.map (flip M₂.∈-resp-list-≈ y∈fx ∘ pres f) x∈xs)

  >>=-∈⁻ : ∀ (f : S₁ ⟶ L₂.setoid) {y} xs →
           y ∈₂ (xs >>= _⟨$⟩_ f) → ∃ λ x → x ∈₁ xs × y ∈₂ f ⟨$⟩ x
  >>=-∈⁻ f xs y∈ = M₁.find (>>=⁻ xs y∈)

  -- _>>=_ is monotone.

  >>=-mono : ∀ (f g : S₁ ⟶ L₂.setoid) {xs ys} →
             xs ⊆₁ ys → (∀ {x} → f ⟨$⟩ x ⊆₂ g ⟨$⟩ x) →
             (xs >>= _⟨$⟩_ f) ⊆₂ (ys >>= _⟨$⟩_ g)
  >>=-mono f g {xs} xs⊆ys f⊆g z∈ with >>=-∈⁻ f xs z∈
  ... | (x , x∈xs , z∈fx) = >>=-∈⁺ g (xs⊆ys x∈xs) (f⊆g z∈fx)

  -- Introduction and elimination rules for _⊛_.

  private

    infixl 4 _⟨⊛⟩_

    _⟨⊛⟩_ : List (S₁ ⟶ S₂) → List S₁.carrier → List S₂.carrier
    fs ⟨⊛⟩ xs = map _⟨$⟩_ fs ⊛ xs

  ⊛-∈⁺ : ∀ f {fs x xs} →
         f ∈₁₂ fs → x ∈₁ xs → f ⟨$⟩ x ∈₂ fs ⟨⊛⟩ xs
  ⊛-∈⁺ _ f∈fs x∈xs =
    ⊛⁺′ (map⁺ (Any.map (λ f≈g x≈y → f≈g x≈y) f∈fs)) x∈xs

  ⊛-∈⁻ : ∀ fs xs {fx} → fx ∈₂ fs ⟨⊛⟩ xs →
         ∃₂ λ f x → f ∈₁₂ fs × x ∈₁ xs × fx ≈₂ f ⟨$⟩ x
  ⊛-∈⁻ fs xs fx∈ with M₁₂.find $ map⁻ (⊛⁻ (map _⟨$⟩_ fs) xs fx∈)
  ... | (f , f∈fs , x∈) with M₁.find x∈
  ...   | (x , x∈xs , fx≈fx) = (f , x , f∈fs , x∈xs , fx≈fx)

  -- _⊛_ is monotone.

  _⊛-mono_ : ∀ {fs gs xs ys} →
             fs ⊆₁₂ gs → xs ⊆₁ ys → fs ⟨⊛⟩ xs ⊆₂ gs ⟨⊛⟩ ys
  _⊛-mono_ {fs = fs} {xs = xs} fs⊆gs xs⊆ys fx∈ with ⊛-∈⁻ fs xs fx∈
  ... | (f , x , f∈fs , x∈xs , fx≈fx) =
    Any.map (S₂.trans fx≈fx) $ ⊛-∈⁺ f (fs⊆gs {f} f∈fs) (xs⊆ys x∈xs)

  -- _⊗_ is monotone.

  _⊗-mono_ : ∀ {xs₁ xs₂ ys₁ ys₂} →
             xs₁ ⊆₁ ys₁ → xs₂ ⊆₂ ys₂ → (xs₁ ⊗ xs₂) ⊆₁,₂ (ys₁ ⊗ ys₂)
  _⊗-mono_ {xs₁ = xs₁} {xs₂} xs₁⊆ys₁ xs₂⊆ys₂ {x , y} x,y∈
    with ⊗⁻′ {P = _≈₁_ x} {Q = _≈₂_ y} xs₁ xs₂ x,y∈
  ... | (x∈ , y∈) = ⊗⁺′ (xs₁⊆ys₁ x∈) (xs₂⊆ys₂ y∈)

------------------------------------------------------------------------
-- Lemmas related to the variant of _∈_ which is defined using
-- propositional equality

module Membership-≡ where

  open Any.Membership-≡
  private
    module P {A} = ListEq.PropositionalEquality {A}
    open module M₁ {A} = Membership₁ (PropEq.setoid A) public
      using (_++-mono_; ++-idempotent;
             map-with-∈-∈⁺; map-with-∈-∈⁻; map-with-∈-mono)
    open module M₂ {A} {B} =
      Membership₂ (PropEq.setoid A) (PropEq.setoid B) public
      using (map-∈⁻)

  -- Any is monotone.

  mono : ∀ {A xs ys} {P : Pred A} → xs ⊆ ys → Any P xs → Any P ys
  mono {P = P} = M₁.mono (PropEq.subst P)

  -- Introduction and elimination rules for concat.

  concat-∈⁺ : ∀ {A} {x : A} {xs xss} →
              x ∈ xs → xs ∈ xss → x ∈ concat xss
  concat-∈⁺ x∈xs = M₁.concat-∈⁺ x∈xs ∘ Any.map P.reflexive

  concat-∈⁻ : ∀ {A} {x : A} xss →
              x ∈ concat xss → ∃ λ xs → x ∈ xs × xs ∈ xss
  concat-∈⁻ xss x∈ =
    Prod.map id (Prod.map id (Any.map P.≈⇒≡)) $ M₁.concat-∈⁻ xss x∈

  -- concat is monotone.

  concat-mono : ∀ {A} {xss yss : List (List A)} →
                xss ⊆ yss → concat xss ⊆ concat yss
  concat-mono xss⊆yss =
    M₁.concat-mono (Any.map P.reflexive ∘ xss⊆yss ∘ Any.map P.≈⇒≡)

  -- any is monotone.

  any-mono : ∀ {A} (p : A → Bool) {xs ys} →
             xs ⊆ ys → T (any p xs) → T (any p ys)
  any-mono p = M₁.any-mono p (PropEq.subst (T ∘₀ p))

  -- Introduction rule for map.

  map-∈⁺ : ∀ {A B} {f : A → B} {x xs} →
           x ∈ xs → f x ∈ map f xs
  map-∈⁺ {f = f} = M₂.map-∈⁺ (PropEq.→-to-⟶ f)

  -- map is monotone.

  map-mono : ∀ {A B} {f : A → B} {xs ys} →
             xs ⊆ ys → map f xs ⊆ map f ys
  map-mono {f = f} = M₂.map-mono (PropEq.→-to-⟶ f)

  -- Introduction and elimination rules for _>>=_.

  private

    [→-to-⟶] : ∀ {A B} → (A → List B) →
               PropEq.setoid A ⟶
               ListEq.Equality.setoid (PropEq.setoid B)
    [→-to-⟶] f =
      record { _⟨$⟩_ = f; pres = P.reflexive ∘ PropEq.cong f }

  >>=-∈⁺ : ∀ {A B} (f : A → List B) {x y xs} →
           x ∈ xs → y ∈ f x → y ∈ (xs >>= f)
  >>=-∈⁺ f = M₂.>>=-∈⁺ ([→-to-⟶] f)

  >>=-∈⁻ : ∀ {A B} (f : A → List B) {y} xs →
           y ∈ (xs >>= f) → ∃ λ x → x ∈ xs × y ∈ f x
  >>=-∈⁻ f = M₂.>>=-∈⁻ ([→-to-⟶] f)

  -- _>>=_ is monotone.

  _>>=-mono_ : ∀ {A B} {f g : A → List B} {xs ys} →
               xs ⊆ ys → (∀ {x} → f x ⊆ g x) →
               (xs >>= f) ⊆ (ys >>= g)
  _>>=-mono_ {f = f} {g} = M₂.>>=-mono ([→-to-⟶] f) ([→-to-⟶] g)

  -- Introduction and elimination rules for _⊛_.

  ⊛-∈⁺ : ∀ {A B} {fs : List (A → B)} {xs f x} →
         f ∈ fs → x ∈ xs → f x ∈ fs ⊛ xs
  ⊛-∈⁺ f∈fs x∈xs =
    ⊛⁺′ (Any.map (λ f≡g x≡y → PropEq.cong₂ _$_ f≡g x≡y) f∈fs) x∈xs

  ⊛-∈⁻ : ∀ {A B} (fs : List (A → B)) xs {fx} →
         fx ∈ fs ⊛ xs → ∃₂ λ f x → f ∈ fs × x ∈ xs × fx ≡ f x
  ⊛-∈⁻ fs xs fx∈ with find $ ⊛⁻ fs xs fx∈
  ... | (f , f∈fs , x∈) with find x∈
  ...   | (x , x∈xs , fx≡fx) = (f , x , f∈fs , x∈xs , fx≡fx)

  -- _⊛_ is monotone.

  _⊛-mono_ : ∀ {A B} {fs gs : List (A → B)} {xs ys} →
             fs ⊆ gs → xs ⊆ ys → fs ⊛ xs ⊆ gs ⊛ ys
  _⊛-mono_ {fs = fs} {xs = xs} fs⊆gs xs⊆ys fx∈ with ⊛-∈⁻ fs xs fx∈
  ... | (f , x , f∈fs , x∈xs , refl) =
    ⊛-∈⁺ (fs⊆gs f∈fs) (xs⊆ys x∈xs)

  -- Introduction and elimination rules for _⊗_.

  private

    lemma₁ : ∀ {A B} {p q : A × B} →
             (p ⟨ _≡_ on₁ proj₁ ⟩₁ q) × (p ⟨ _≡_ on₁ proj₂ ⟩₁ q) → p ≡ q
    lemma₁ {p = (x , y)} {q = (.x , .y)} (refl , refl) = refl

    lemma₂ : ∀ {A B} {p q : A × B} →
             p ≡ q → (p ⟨ _≡_ on₁ proj₁ ⟩₁ q) × (p ⟨ _≡_ on₁ proj₂ ⟩₁ q)
    lemma₂ = < PropEq.cong proj₁ , PropEq.cong proj₂ >

  ⊗-∈⁺ : ∀ {A B} {xs : List A} {ys : List B} {x y} →
         x ∈ xs → y ∈ ys → (x , y) ∈ (xs ⊗ ys)
  ⊗-∈⁺ x∈xs y∈ys = Any.map lemma₁ (⊗⁺′ x∈xs y∈ys)

  ⊗-∈⁻ : ∀ {A B} (xs : List A) (ys : List B) {p} →
         p ∈ (xs ⊗ ys) → proj₁ p ∈ xs × proj₂ p ∈ ys
  ⊗-∈⁻ xs ys = ⊗⁻′ xs ys ∘ Any.map lemma₂

  -- _⊗_ is monotone.

  _⊗-mono_ : ∀ {A B} {xs₁ ys₁ : List A} {xs₂ ys₂ : List B} →
             xs₁ ⊆ ys₁ → xs₂ ⊆ ys₂ → (xs₁ ⊗ xs₂) ⊆ (ys₁ ⊗ ys₂)
  _⊗-mono_ xs₁⊆ys₁ xs₂⊆ys₂ {p} =
    Any.map lemma₁ ∘ M₂._⊗-mono_ xs₁⊆ys₁ xs₂⊆ys₂ {p} ∘ Any.map lemma₂
