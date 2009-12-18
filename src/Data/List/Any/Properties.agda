------------------------------------------------------------------------
-- Properties relating Any to various list functions
------------------------------------------------------------------------

module Data.List.Any.Properties where

open import Algebra
open import Category.Monad
open import Data.Bool
open import Data.Bool.Properties
open import Data.Empty
open import Data.Function
open import Data.List as List
open RawMonad List.monad
open import Data.List.Any as Any using (Any; here; there)
open import Data.Nat as Nat
import Data.Nat.Properties as NatProp
open import Data.Product as Prod hiding (map)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Level
open import Relation.Unary using ( _⟨×⟩_; _⟨→⟩_) renaming (_⊆_ to _⋐_)
open import Relation.Binary
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.FunctionSetoid as FunS
  using (_⟶_; _⟨$⟩_; _⇨_)
import Relation.Binary.List.Pointwise as ListEq
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)
open import Relation.Binary.Product.Pointwise
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl; inspect; _with-≡_)
import Relation.Binary.Props.DecTotalOrder as DTOProps
open import Relation.Nullary
import Relation.Nullary.Injection as Inj
open import Relation.Nullary.Negation

------------------------------------------------------------------------
-- Lemmas related to Any

-- Any.map is functorial.

map-id : ∀ {A} {P : A → Set} (f : P ⋐ P) {xs} →
         (∀ {x} (p : P x) → f p ≡ p) →
         (p : Any P xs) → Any.map f p ≡ p
map-id f hyp (here  p) = P.cong here (hyp p)
map-id f hyp (there p) = P.cong there $ map-id f hyp p

map-∘ : ∀ {A} {P Q R : A → Set} (f : Q ⋐ R) (g : P ⋐ Q)
        {xs} (p : Any P xs) →
        Any.map (f ∘ g) p ≡ Any.map f (Any.map g p)
map-∘ f g (here  p) = refl
map-∘ f g (there p) = P.cong there $ map-∘ f g p

-- Introduction (⁺) and elimination (⁻) rules for map.

map⁺ : ∀ {A B} {P : B → Set} {f : A → B} {xs} →
       Any (P ∘ f) xs → Any P (map f xs)
map⁺ (here p)  = here p
map⁺ (there p) = there $ map⁺ p

map⁻ : ∀ {A B} {P : B → Set} {f : A → B} {xs} →
       Any P (map f xs) → Any (P ∘ f) xs
map⁻ {xs = []}     ()
map⁻ {xs = x ∷ xs} (here p)  = here p
map⁻ {xs = x ∷ xs} (there p) = there $ map⁻ p

-- The rules are inverses.

map⁺∘map⁻ : ∀ {A B : Set} {P : B → Set} {f : A → B} {xs} →
            (p : Any P (List.map f xs)) →
            map⁺ (map⁻ p) ≡ p
map⁺∘map⁻ {xs = []}     ()
map⁺∘map⁻ {xs = x ∷ xs} (here  p) = refl
map⁺∘map⁻ {xs = x ∷ xs} (there p) = P.cong there (map⁺∘map⁻ p)

map⁻∘map⁺ : ∀ {A B} (P : B → Set) {f : A → B} {xs} →
            (p : Any (P ∘ f) xs) →
            map⁻ {P = P} (map⁺ p) ≡ p
map⁻∘map⁺ P (here  p) = refl
map⁻∘map⁺ P (there p) = P.cong there (map⁻∘map⁺ P p)

-- Introduction and elimination rules for _++_.

++⁺ˡ : ∀ {A} {P : A → Set} {xs ys} →
       Any P xs → Any P (xs ++ ys)
++⁺ˡ (here p)  = here p
++⁺ˡ (there p) = there (++⁺ˡ p)

++⁺ʳ : ∀ {A} {P : A → Set} xs {ys} →
       Any P ys → Any P (xs ++ ys)
++⁺ʳ []       p = p
++⁺ʳ (x ∷ xs) p = there (++⁺ʳ xs p)

++⁻ : ∀ {A} {P : A → Set} xs {ys} →
      Any P (xs ++ ys) → Any P xs ⊎ Any P ys
++⁻ []       p         = inj₂ p
++⁻ (x ∷ xs) (here p)  = inj₁ (here p)
++⁻ (x ∷ xs) (there p) = Sum.map there id (++⁻ xs p)

-- The rules are inverses.

++⁺∘++⁻ : ∀ {A} {P : A → Set} xs {ys}
          (p : Any P (xs ++ ys)) →
          [ ++⁺ˡ , ++⁺ʳ xs ]′ (++⁻ xs p) ≡ p
++⁺∘++⁻ []       p         = refl
++⁺∘++⁻ (x ∷ xs) (here  p) = refl
++⁺∘++⁻ (x ∷ xs) (there p) with ++⁻ xs p | ++⁺∘++⁻ xs p
++⁺∘++⁻ (x ∷ xs) (there p) | inj₁ p′ | ih = P.cong there ih
++⁺∘++⁻ (x ∷ xs) (there p) | inj₂ p′ | ih = P.cong there ih

++⁻∘++⁺ : ∀ {A} {P : A → Set} xs {ys} (p : Any P xs ⊎ Any P ys) →
          ++⁻ xs ([ ++⁺ˡ , ++⁺ʳ xs ]′ p) ≡ p
++⁻∘++⁺ []            (inj₁ ())
++⁻∘++⁺ []            (inj₂ p)         = refl
++⁻∘++⁺ (x ∷ xs)      (inj₁ (here  p)) = refl
++⁻∘++⁺ (x ∷ xs) {ys} (inj₁ (there p)) rewrite ++⁻∘++⁺ xs {ys} (inj₁ p) = refl
++⁻∘++⁺ (x ∷ xs)      (inj₂ p)         rewrite ++⁻∘++⁺ xs      (inj₂ p) = refl

-- Introduction and elimination rules for return.

return⁺ : ∀ {A} {P : A → Set} {x} →
          P x → Any P (return x)
return⁺ = here

return⁻ : ∀ {A} {P : A → Set} {x} →
          Any P (return x) → P x
return⁻ (here p)   = p
return⁻ (there ())

-- The rules are inverses.

return⁺∘return⁻ : ∀ {A} {P : A → Set} {x} (p : Any P (return x)) →
                  return⁺ (return⁻ p) ≡ p
return⁺∘return⁻ (here p)   = refl
return⁺∘return⁻ (there ())

return⁻∘return⁺ : ∀ {A} {P : A → Set} {x} (p : P x) →
                  return⁻ {P = P} (return⁺ p) ≡ p
return⁻∘return⁺ p = refl

-- Introduction and elimination rules for concat.

concat⁺ : ∀ {A} {P : A → Set} {xss} →
          Any (Any P) xss → Any P (concat xss)
concat⁺ (here p)           = ++⁺ˡ p
concat⁺ (there {x = xs} p) = ++⁺ʳ xs (concat⁺ p)

concat⁻ : ∀ {A} {P : A → Set} xss →
          Any P (concat xss) → Any (Any P) xss
concat⁻ []               ()
concat⁻ ([]       ∷ xss) p         = there $ concat⁻ xss p
concat⁻ ((x ∷ xs) ∷ xss) (here p)  = here (here p)
concat⁻ ((x ∷ xs) ∷ xss) (there p)
  with concat⁻ (xs ∷ xss) p
... | here  p′ = here (there p′)
... | there p′ = there p′

-- The rules are inverses.

concat⁻∘++⁺ˡ : ∀ {A} {P : A → Set} {xs} xss (p : Any P xs) →
               concat⁻ (xs ∷ xss) (++⁺ˡ p) ≡ here p
concat⁻∘++⁺ˡ xss (here  p) = refl
concat⁻∘++⁺ˡ xss (there p) rewrite concat⁻∘++⁺ˡ xss p = refl

concat⁻∘++⁺ʳ : ∀ {A} {P : A → Set} xs xss (p : Any P (concat xss)) →
               concat⁻ (xs ∷ xss) (++⁺ʳ xs p) ≡ there (concat⁻ xss p)
concat⁻∘++⁺ʳ []       xss p = refl
concat⁻∘++⁺ʳ (x ∷ xs) xss p rewrite concat⁻∘++⁺ʳ xs xss p = refl

concat⁺∘concat⁻ : ∀ {A} {P : A → Set} xss (p : Any P (concat xss)) →
                  concat⁺ (concat⁻ xss p) ≡ p
concat⁺∘concat⁻ []               ()
concat⁺∘concat⁻ ([]       ∷ xss) p         = concat⁺∘concat⁻ xss p
concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (here p)  = refl
concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (there p)
  with concat⁻ (xs ∷ xss) p | concat⁺∘concat⁻ (xs ∷ xss) p
concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (there .(++⁺ˡ p′))              | here  p′ | refl = refl
concat⁺∘concat⁻ ((x ∷ xs) ∷ xss) (there .(++⁺ʳ xs (concat⁺ p′))) | there p′ | refl = refl

concat⁻∘concat⁺ : ∀ {A} {P : A → Set} {xss} (p : Any (Any P) xss) →
                  concat⁻ xss (concat⁺ p) ≡ p
concat⁻∘concat⁺ (here                      p) = concat⁻∘++⁺ˡ _ p
concat⁻∘concat⁺ (there {x = xs} {xs = xss} p)
  rewrite concat⁻∘++⁺ʳ xs xss (concat⁺ p) =
    P.cong there $ concat⁻∘concat⁺ p

-- Introduction and elimination rules for _>>=_.

>>=⁺ : ∀ {A B P xs} {f : A → List B} →
       Any (Any P ∘ f) xs → Any P (xs >>= f)
>>=⁺ = concat⁺ ∘ map⁺

>>=⁻ : ∀ {A B P} xs {f : A → List B} →
       Any P (xs >>= f) → Any (Any P ∘ f) xs
>>=⁻ _ = map⁻ ∘ concat⁻ _

-- The rules are inverses.

>>=⁺∘>>=⁻ : ∀ {A B P} xs {f : A → List B} (p : Any P (xs >>= f)) →
            >>=⁺ (>>=⁻ xs p) ≡ p
>>=⁺∘>>=⁻ xs {f} p rewrite map⁺∘map⁻ (concat⁻ (map f xs) p) =
  concat⁺∘concat⁻ (map f xs) p

>>=⁻∘>>=⁺ : ∀ {A B P xs} {f : A → List B} (p : Any (Any P ∘ f) xs) →
            >>=⁻ xs (>>=⁺ p) ≡ p
>>=⁻∘>>=⁺ {P = P} p rewrite concat⁻∘concat⁺ (map⁺ p) =
  map⁻∘map⁺ (Any P) p

-- Introduction and elimination rules for _⊛_.

⊛⁺ : ∀ {A B P} {fs : List (A → B)} {xs} →
     Any (λ f → Any (P ∘ f) xs) fs → Any P (fs ⊛ xs)
⊛⁺ = >>=⁺ ∘ Any.map (>>=⁺ ∘ Any.map return⁺)

⊛⁺′ : ∀ {A B P Q} {fs : List (A → B)} {xs} →
      Any (P ⟨→⟩ Q) fs → Any P xs → Any Q (fs ⊛ xs)
⊛⁺′ pq p = ⊛⁺ (Any.map (λ pq → Any.map (λ {x} → pq {x}) p) pq)

⊛⁻ : ∀ {A B P} (fs : List (A → B)) xs →
     Any P (fs ⊛ xs) → Any (λ f → Any (P ∘ f) xs) fs
⊛⁻ fs xs = Any.map (Any.map return⁻ ∘ >>=⁻ xs) ∘ >>=⁻ fs

-- The rules are inverses.

⊛⁺∘⊛⁻ : ∀ {A B P} (fs : List (A → B))
        xs (p : Any P (fs ⊛ xs)) → ⊛⁺ (⊛⁻ fs xs p) ≡ p
⊛⁺∘⊛⁻ {A} {B} {P} fs xs p = begin
  ⊛⁺ (⊛⁻ fs xs p)                                                  ≡⟨ P.cong >>=⁺ $ P.sym $
                                                                        map-∘ (>>=⁺ {P = P} ∘ Any.map return⁺)
                                                                              (Any.map return⁻ ∘ >>=⁻ {P = P} xs)
                                                                              (>>=⁻ fs p) ⟩
  >>=⁺ (Any.map (>>=⁺ {P = P} ∘ Any.map return⁺ ∘
                 Any.map return⁻ ∘ >>=⁻ {P = P} xs)
                (>>=⁻ fs p))                                       ≡⟨ P.cong >>=⁺ (flip (map-id _) (>>=⁻ fs p) (λ p′ → begin

    >>=⁺ (Any.map return⁺ (Any.map (return⁻ {P = P}) (>>=⁻ xs p′)))  ≡⟨ P.cong >>=⁺ $ P.sym $
                                                                          map-∘ return⁺ (return⁻ {P = P}) (>>=⁻ xs p′) ⟩
    >>=⁺ (Any.map (return⁺ ∘′ return⁻ {P = P}) (>>=⁻ xs p′))         ≡⟨ P.cong >>=⁺ (map-id _ return⁺∘return⁻ (>>=⁻ xs p′)) ⟩
    >>=⁺ (>>=⁻ xs p′)                                                ≡⟨ >>=⁺∘>>=⁻ xs p′ ⟩
    p′                                                               ∎)) ⟩

  >>=⁺ (>>=⁻ fs p)                                                 ≡⟨ >>=⁺∘>>=⁻ fs p ⟩
  p                                                                ∎
  where open P.≡-Reasoning

⊛⁻∘⊛⁺ : ∀ {A B} {P : B → Set} {fs : List (A → B)} {xs}
        (p : Any (λ f → Any (P ∘ f) xs) fs) →
        ⊛⁻ {P = P} fs xs (⊛⁺ p) ≡ p
⊛⁻∘⊛⁺ {P = P} {fs} {xs} p =
  helper₁ (>>=⁻∘>>=⁺ (Any.map (>>=⁺ {P = P} ∘ Any.map return⁺) p))
  where
  open P.≡-Reasoning

  helper₂ : ∀ {f} (p : Any (P ∘ f) xs) →
            Any.map return⁻ (>>=⁻ {P = P} xs
                            (>>=⁺ (Any.map return⁺ p))) ≡ p
  helper₂ p rewrite >>=⁻∘>>=⁺ {P = P} (Any.map return⁺ p) = begin
    Any.map return⁻ (Any.map return⁺ p) ≡⟨ P.sym (map-∘ (return⁻ {P = P}) return⁺ p) ⟩
    Any.map id p                        ≡⟨ map-id id (λ _ → refl) p ⟩
    p                                   ∎

  helper₁ : ∀ {p′} →
            p′ ≡ Any.map (>>=⁺ {P = P} ∘ Any.map return⁺) p →
            Any.map (Any.map return⁻ ∘ >>=⁻ xs) p′ ≡ p
  helper₁ refl
    rewrite P.sym (map-∘ (Any.map return⁻ ∘ >>=⁻ xs)
                         (>>=⁺ {P = P} ∘ Any.map return⁺) p) =
      map-id _ helper₂ p

-- Introduction and elimination rules for _⊗_.

⊗⁺ : ∀ {A B P} {xs : List A} {ys : List B} →
     Any (λ x → Any (λ y → P (x , y)) ys) xs → Any P (xs ⊗ ys)
⊗⁺ = ⊛⁺ ∘′ ⊛⁺ ∘′ return⁺

⊗⁺′ : ∀ {A B} {P : A → Set} {Q : B → Set} {xs ys} →
      Any P xs → Any Q ys → Any (P ⟨×⟩ Q) (xs ⊗ ys)
⊗⁺′ p q = ⊗⁺ (Any.map (λ p → Any.map (λ q → (p , q)) q) p)

⊗⁻ : ∀ {A B P} (xs : List A) (ys : List B) →
     Any P (xs ⊗ ys) → Any (λ x → Any (λ y → P (x , y)) ys) xs
⊗⁻ _ _ = return⁻ ∘ ⊛⁻ _ _ ∘ ⊛⁻ _ _

⊗⁻′ : ∀ {A B} {P : A → Set} {Q : B → Set} xs ys →
      Any (P ⟨×⟩ Q) (xs ⊗ ys) → Any P xs × Any Q ys
⊗⁻′ _ _ pq =
  (Any.map (proj₁ ∘ proj₂ ∘ Any.satisfied) lem ,
   (Any.map proj₂ $ proj₂ (Any.satisfied lem)))
  where lem = ⊗⁻ _ _ pq

-- Any and any are related via T.

any⁺ : ∀ {A} (p : A → Bool) {xs} →
       Any (T ∘ p) xs → T (any p xs)
any⁺ p (here  px)          = proj₂ T-∨ (inj₁ px)
any⁺ p (there {x = x} pxs) with p x
... | true  = _
... | false = any⁺ p pxs

any⁻ : ∀ {A} (p : A → Bool) xs →
       T (any p xs) → Any (T ∘ p) xs
any⁻ p []       ()
any⁻ p (x ∷ xs) px∷xs with inspect (p x)
any⁻ p (x ∷ xs) px∷xs | true  with-≡ eq = here (proj₂ T-≡ $ P.sym eq)
any⁻ p (x ∷ xs) px∷xs | false with-≡ eq with p x
any⁻ p (x ∷ xs) pxs   | false with-≡ refl | .false =
  there (any⁻ p xs pxs)

------------------------------------------------------------------------
-- Lemmas related to _∈_, parameterised on underlying equalities

module Membership₁ (S : Setoid zero zero) where

  open Any.Membership S
  private
    open module S = Setoid S using (_≈_)
    open module [M] = Any.Membership (ListEq.setoid S)
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

  -- _++_ is commutative.

  ++-comm : ∀ xs ys → xs ++ ys ⊆ ys ++ xs
  ++-comm xs ys = [ ++⁺ʳ ys , ++⁺ˡ ]′ ∘ ++⁻ xs

  -- Introduction and elimination rules for concat.

  concat-∈⁺ : ∀ {x xs xss} →
              x ∈ xs → xs [∈] xss → x ∈ concat xss
  concat-∈⁺ x∈xs xs∈xss =
    concat⁺ (Any.map (λ xs≈ys → Pre.reflexive xs≈ys x∈xs) xs∈xss)
    where module Pre = Preorder ⊆-preorder

  concat-∈⁻ : ∀ {x} xss → x ∈ concat xss →
              ∃ λ xs → x ∈ xs × xs [∈] xss
  concat-∈⁻ xss x∈ = Prod.map id swap $ [M].find (concat⁻ xss x∈)

  -- concat is monotone.

  concat-mono : ∀ {xss yss} →
                xss [⊆] yss → concat xss ⊆ concat yss
  concat-mono {xss = xss} xss⊆yss x∈ with concat-∈⁻ xss x∈
  ... | (xs , x∈xs , xs∈xss) = concat-∈⁺ x∈xs (xss⊆yss xs∈xss)

  -- any is monotone.

  any-mono : ∀ p → (T ∘ p) Respects _≈_ →
             ∀ {xs ys} → xs ⊆ ys → T (any p xs) → T (any p ys)
  any-mono p resp xs⊆ys = any⁺ p ∘ mono resp xs⊆ys ∘ any⁻ p _

  -- Introduction and elimination rules for map-with-∈.

  map-with-∈-∈⁺ : ∀ {A} {xs : List A}
                  (f : ∀ {x} → x ∈≡ xs → S.Carrier) {x} →
                  (x∈xs : x ∈≡ xs) → f x∈xs ∈ M≡.map-with-∈ xs f
  map-with-∈-∈⁺ f (here refl)  = here S.refl
  map-with-∈-∈⁺ f (there x∈xs) = there $ map-with-∈-∈⁺ (f ∘ there) x∈xs

  map-with-∈-∈⁻ : ∀ {A} {xs : List A}
                  (f : ∀ {x} → x ∈≡ xs → S.Carrier) {fx∈xs} →
                  fx∈xs ∈ M≡.map-with-∈ xs f →
                  ∃ λ x → Σ (x ∈≡ xs) λ x∈xs → fx∈xs ≈ f x∈xs
  map-with-∈-∈⁻ {xs = []}     f ()
  map-with-∈-∈⁻ {xs = y ∷ xs} f (here fx≈)   = (y , here refl , fx≈)
  map-with-∈-∈⁻ {xs = y ∷ xs} f (there x∈xs) =
    Prod.map id (Prod.map there id) $ map-with-∈-∈⁻ (f ∘ there) x∈xs

  -- map-with-∈ is monotone.

  map-with-∈-mono :
    ∀ {A} {xs : List A} {f : ∀ {x} → x ∈≡ xs → S.Carrier}
          {ys : List A} {g : ∀ {x} → x ∈≡ ys → S.Carrier} →
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

  -- Only a finite number of distinct elements can be members of a
  -- given list.

  finite : (f : Inj.Injection (P.setoid ℕ) S) →
           ∀ xs → ¬ (∀ i → Inj.Injection.to f ⟨$⟩ i ∈ xs)
  finite inj []       ∈[]   with ∈[] zero
  ... | ()
  finite inj (x ∷ xs) ∈x∷xs = excluded-middle helper
    where
    open Inj.Injection inj

    module DTO = DecTotalOrder Nat.decTotalOrder
    module STO = StrictTotalOrder
                   (DTOProps.strictTotalOrder Nat.decTotalOrder)
    module CS  = CommutativeSemiring NatProp.commutativeSemiring

    not-x : ∀ {i} → ¬ (to ⟨$⟩ i ≈ x) → to ⟨$⟩ i ∈ xs
    not-x {i} ≉x with ∈x∷xs i
    ... | here  ≈x  = ⊥-elim (≉x ≈x)
    ... | there ∈xs = ∈xs

    helper : ¬ Dec (∃ λ i → to ⟨$⟩ i ≈ x)
    helper (no ≉x)        = finite inj  xs (λ i → not-x (≉x ∘ _,_ i))
    helper (yes (i , ≈x)) = finite inj′ xs ∈xs
      where
      open P

      f : ℕ → S.Carrier
      f j with STO.compare i j
      f j | tri< _ _ _ = to ⟨$⟩ suc j
      f j | tri≈ _ _ _ = to ⟨$⟩ suc j
      f j | tri> _ _ _ = to ⟨$⟩ j

      ∈-if-not-i : ∀ {j} → i ≢ j → to ⟨$⟩ j ∈ xs
      ∈-if-not-i i≢j = not-x (i≢j ∘ injective ∘ S.trans ≈x ∘ S.sym)

      lemma : ∀ {k j} → k ≤ j → suc j ≢ k
      lemma 1+j≤j refl = NatProp.1+n≰n 1+j≤j

      ∈xs : ∀ j → f j ∈ xs
      ∈xs j with STO.compare i j
      ∈xs j  | tri< (i≤j , _) _ _ = ∈-if-not-i (lemma i≤j ∘ sym)
      ∈xs j  | tri> _ i≢j _       = ∈-if-not-i i≢j
      ∈xs .i | tri≈ _ refl _      =
        ∈-if-not-i (NatProp.m≢1+m+n i ∘
                    subst (_≡_ i ∘ suc) (sym $ proj₂ CS.+-identity i))

      injective′ : Inj.Injective {B = S} (→-to-⟶ f)
      injective′ {j} {k} eq with STO.compare i j | STO.compare i k
      ... | tri< _ _ _         | tri< _ _ _         = cong pred                                   $ injective eq
      ... | tri< _ _ _         | tri≈ _ _ _         = cong pred                                   $ injective eq
      ... | tri< (i≤j , _) _ _ | tri> _ _ (k≤i , _) = ⊥-elim (lemma (DTO.trans k≤i i≤j)           $ injective eq)
      ... | tri≈ _ _ _         | tri< _ _ _         = cong pred                                   $ injective eq
      ... | tri≈ _ _ _         | tri≈ _ _ _         = cong pred                                   $ injective eq
      ... | tri≈ _ i≡j _       | tri> _ _ (k≤i , _) = ⊥-elim (lemma (subst (_≤_ k) i≡j k≤i)       $ injective eq)
      ... | tri> _ _ (j≤i , _) | tri< (i≤k , _) _ _ = ⊥-elim (lemma (DTO.trans j≤i i≤k)     $ sym $ injective eq)
      ... | tri> _ _ (j≤i , _) | tri≈ _ i≡k _       = ⊥-elim (lemma (subst (_≤_ j) i≡k j≤i) $ sym $ injective eq)
      ... | tri> _ _ (j≤i , _) | tri> _ _ (k≤i , _) =                                               injective eq

      inj′ = record { to = →-to-⟶ f; injective = injective′ }

module Membership₂ (S₁ S₂ : Setoid zero zero) where

  private
    open module S₁ = Setoid S₁ using () renaming (_≈_ to _≈₁_)
    open module S₂ = Setoid S₂ using () renaming (_≈_ to _≈₂_)
    LS₂            = ListEq.setoid S₂
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
  map-∈⁺ f = map⁺ ∘ Any.map (FunS.cong f)

  map-∈⁻ : ∀ {f fx} xs →
           fx ∈₂ map f xs → ∃ λ x → x ∈₁ xs × fx ≈₂ f x
  map-∈⁻ _ fx∈ = M₁.find (map⁻ fx∈)

  -- map is monotone.

  map-mono : ∀ (f : S₁ ⟶ S₂) {xs ys} →
             xs ⊆₁ ys → map (_⟨$⟩_ f) xs ⊆₂ map (_⟨$⟩_ f) ys
  map-mono f xs⊆ys fx∈ with map-∈⁻ _ fx∈
  ... | (x , x∈ , eq) = Any.map (S₂.trans eq) (map-∈⁺ f (xs⊆ys x∈))

  -- Introduction and elimination rules for _>>=_.

  >>=-∈⁺ : ∀ (f : S₁ ⟶ LS₂) {x y xs} →
           x ∈₁ xs → y ∈₂ f ⟨$⟩ x → y ∈₂ (xs >>= _⟨$⟩_ f)
  >>=-∈⁺ f x∈xs y∈fx =
    >>=⁺ (Any.map (flip M₂.∈-resp-list-≈ y∈fx ∘ FunS.cong f) x∈xs)

  >>=-∈⁻ : ∀ (f : S₁ ⟶ LS₂) {y} xs →
           y ∈₂ (xs >>= _⟨$⟩_ f) → ∃ λ x → x ∈₁ xs × y ∈₂ f ⟨$⟩ x
  >>=-∈⁻ f xs y∈ = M₁.find (>>=⁻ xs y∈)

  -- _>>=_ is monotone.

  >>=-mono : ∀ (f g : S₁ ⟶ LS₂) {xs ys} →
             xs ⊆₁ ys → (∀ {x} → f ⟨$⟩ x ⊆₂ g ⟨$⟩ x) →
             (xs >>= _⟨$⟩_ f) ⊆₂ (ys >>= _⟨$⟩_ g)
  >>=-mono f g {xs} xs⊆ys f⊆g z∈ with >>=-∈⁻ f xs z∈
  ... | (x , x∈xs , z∈fx) = >>=-∈⁺ g (xs⊆ys x∈xs) (f⊆g z∈fx)

  -- Introduction and elimination rules for _⊛_.

  private

    infixl 4 _⟨⊛⟩_

    _⟨⊛⟩_ : List (S₁ ⟶ S₂) → List S₁.Carrier → List S₂.Carrier
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
    module S {A} = Setoid (ListEq.setoid (P.setoid A))
    module M {A} = Any.Membership (P.setoid A)
    open module M₁ {A} = Membership₁ (P.setoid A) public
      using (_++-mono_; ++-idempotent; ++-comm;
             map-with-∈-∈⁺; map-with-∈-∈⁻; map-with-∈-mono;
             finite)
    open module M₂ {A} {B} =
      Membership₂ (P.setoid A) (P.setoid B) public
      using (map-∈⁻)

  -- Any is monotone.

  mono : ∀ {A xs ys} {P : A → Set} → xs ⊆ ys → Any P xs → Any P ys
  mono {P = P} = M₁.mono (P.subst P)

  -- Any.map is related to find.

  map∘find : ∀ {A : Set} {P : A → Set} {xs}
             (p : Any P xs) → let p′ = find p in
             {f : _≡_ (proj₁ p′) ⋐ P} →
             f refl ≡ proj₂ (proj₂ p′) →
             Any.map f (proj₁ (proj₂ p′)) ≡ p
  map∘find (here  p) hyp = P.cong here  hyp
  map∘find (there p) hyp = P.cong there (map∘find p hyp)

  find∘map : ∀ {A : Set} {P : A → Set} {x : A} {xs}
             (x∈xs : x ∈ xs) (f : _≡_ x ⋐ P) →
             find (Any.map f x∈xs) ≡ (x , x∈xs , f refl)
  find∘map (here  refl) f = refl
  find∘map (there x∈xs) f rewrite find∘map x∈xs f = refl

  -- Introduction and elimination rules for concat.

  concat-∈⁺ : ∀ {A} {x : A} {xs xss} →
              x ∈ xs → xs ∈ xss → x ∈ concat xss
  concat-∈⁺ x∈xs = M₁.concat-∈⁺ x∈xs ∘ Any.map S.reflexive

  concat-∈⁻ : ∀ {A} {x : A} xss →
              x ∈ concat xss → ∃ λ xs → x ∈ xs × xs ∈ xss
  concat-∈⁻ xss x∈ =
    Prod.map id (Prod.map id (Any.map ListEq.Rel≡⇒≡)) $
      M₁.concat-∈⁻ xss x∈

  -- concat is monotone.

  concat-mono : ∀ {A} {xss yss : List (List A)} →
                xss ⊆ yss → concat xss ⊆ concat yss
  concat-mono xss⊆yss =
    M₁.concat-mono (Any.map S.reflexive ∘ xss⊆yss ∘
                    Any.map ListEq.Rel≡⇒≡)

  -- any is monotone.

  any-mono : ∀ {A} (p : A → Bool) {xs ys} →
             xs ⊆ ys → T (any p xs) → T (any p ys)
  any-mono p = M₁.any-mono p (P.subst (T ∘ p))

  -- Introduction rule for map.

  map-∈⁺ : ∀ {A B} {f : A → B} {x xs} →
           x ∈ xs → f x ∈ map f xs
  map-∈⁺ {f = f} = M₂.map-∈⁺ (P.→-to-⟶ f)

  -- The introduction and elimination rules are inverses (more or
  -- less).

  map-∈⁺∘map-∈⁻ : ∀ {A B : Set} {f : A → B} {fx xs}
                  (p : fx ∈ List.map f xs) →
                  map-∈⁺ {f = f} (proj₁ (proj₂ (map-∈⁻ xs p))) ≅ p
  map-∈⁺∘map-∈⁻ {xs = []}     ()
  map-∈⁺∘map-∈⁻ {xs = x ∷ xs} (here refl) = refl
  map-∈⁺∘map-∈⁻ {xs = x ∷ xs} (there p)   = there-cong (map-∈⁺∘map-∈⁻ p)
    where
    there-cong : ∀ {A : Set} {P Q : A → Set} {x xs}
                   {p : Any P xs} {q : Any Q xs} →
                 p ≅ q → there {x = x} p ≅ there {x = x} q
    there-cong refl = refl

  map-∈⁻∘map-∈⁺ : ∀ {A B : Set} (f : A → B) {x xs} (x∈xs : x ∈ xs) →
                  map-∈⁻ xs (map-∈⁺ {f = f} x∈xs) ≡ (x , x∈xs , refl)
  map-∈⁻∘map-∈⁺ {B = B} f {x} x∈xs = begin
    find (map⁻ {P = _≡_ _} $
          map⁺ (Any.map f-cong x∈xs))  ≡⟨ P.cong find $
                                            map⁻∘map⁺ (_≡_ _) (Any.map f-cong x∈xs) ⟩
    find (Any.map f-cong x∈xs)         ≡⟨ find∘map x∈xs f-cong ⟩
    (x , x∈xs , refl)                  ∎
    where
    open P.≡-Reasoning

    f-cong : _≡_ =[ f ]⇒ _≡_
    f-cong = FunS.cong (P.→-to-⟶ {B = P.setoid B} f)

  -- map is monotone.

  map-mono : ∀ {A B} {f : A → B} {xs ys} →
             xs ⊆ ys → map f xs ⊆ map f ys
  map-mono {f = f} = M₂.map-mono (P.→-to-⟶ f)

  -- Introduction and elimination rules for _>>=_.

  >>=-∈⁺ : ∀ {A B} (f : A → List B) {x y xs} →
           x ∈ xs → y ∈ f x → y ∈ (xs >>= f)
  >>=-∈⁺ f = M₂.>>=-∈⁺ (P.→-to-⟶ f)

  >>=-∈⁻ : ∀ {A B} (f : A → List B) {y} xs →
           y ∈ (xs >>= f) → ∃ λ x → x ∈ xs × y ∈ f x
  >>=-∈⁻ f = M₂.>>=-∈⁻ (P.→-to-⟶ f)

  -- The introduction and elimination rules are inverses (more or
  -- less).

  private

    lift-resp-id : ∀ {A : Set} {x : A} {xs} xs≈ys (p : x ∈ xs) →
                   M.∈-resp-list-≈ xs≈ys p ≡ p
    lift-resp-id ListEq.[]               ()
    lift-resp-id (ListEq._∷_ refl xs≈ys) (here  refl) = refl
    lift-resp-id (ListEq._∷_ refl xs≈ys) (there p)    =
      P.cong there (lift-resp-id xs≈ys p)

  >>=-∈⁺∘>>=-∈⁻ : ∀ {A B : Set} (f : A → List B) {y} xs
                  (p : y ∈ (xs >>= f)) →
                  let p′ = proj₂ $ >>=-∈⁻ f xs p in
                  >>=-∈⁺ f (proj₁ p′) (proj₂ p′) ≡ p
  >>=-∈⁺∘>>=-∈⁻ f xs p = begin
    >>=⁺ (Any.map _ (proj₁ (proj₂ (find (>>=⁻ xs p)))))  ≡⟨ P.cong >>=⁺ $
                                                              map∘find (>>=⁻ xs p) (lift-resp-id _ _) ⟩
    >>=⁺ (>>=⁻ xs p)                                     ≡⟨ >>=⁺∘>>=⁻ xs p ⟩
    p                                                    ∎
    where open P.≡-Reasoning

  >>=-∈⁻∘>>=-∈⁺ : ∀ {A B : Set} (f : A → List B) {x y xs}
                  (x∈xs : x ∈ xs) (y∈fx : y ∈ f x) →
                  >>=-∈⁻ f xs (>>=-∈⁺ f x∈xs y∈fx) ≡ (x , x∈xs , y∈fx)
  >>=-∈⁻∘>>=-∈⁺ f {x = x} {xs = xs} x∈xs y∈fx = begin
    find (>>=⁻ xs (>>=⁺ (Any.map _ x∈xs)))  ≡⟨ P.cong find (>>=⁻∘>>=⁺ (Any.map _ x∈xs)) ⟩
    find (Any.map _ x∈xs)                   ≡⟨ find∘map x∈xs _ ⟩
    (x , x∈xs , _)                          ≡⟨ P.cong (λ p → (x , x∈xs , p)) (lift-resp-id _ _) ⟩
    (x , x∈xs , y∈fx)                       ∎
    where open P.≡-Reasoning

  -- _>>=_ is monotone.

  _>>=-mono_ : ∀ {A B} {f g : A → List B} {xs ys} →
               xs ⊆ ys → (∀ {x} → f x ⊆ g x) →
               (xs >>= f) ⊆ (ys >>= g)
  _>>=-mono_ {f = f} {g} =
    M₂.>>=-mono (P.→-to-⟶ f) (P.→-to-⟶ g)

  -- Introduction and elimination rules for _⊛_.

  ⊛-∈⁺ : ∀ {A B} {fs : List (A → B)} {xs f x} →
         f ∈ fs → x ∈ xs → f x ∈ fs ⊛ xs
  ⊛-∈⁺ f∈fs x∈xs =
    ⊛⁺′ (Any.map (λ f≡g x≡y → P.cong₂ _$_ f≡g x≡y) f∈fs) x∈xs

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

    lemma₁ : {A B : Set} {p q : A × B} →
             (p ⟨ _≡_ on proj₁ ⟩ q) × (p ⟨ _≡_ on proj₂ ⟩ q) → p ≡ q
    lemma₁ {p = (x , y)} {q = (.x , .y)} (refl , refl) = refl

    lemma₂ : {A B : Set} {p q : A × B} →
             p ≡ q → (p ⟨ _≡_ on proj₁ ⟩ q) × (p ⟨ _≡_ on proj₂ ⟩ q)
    lemma₂ = < P.cong proj₁ , P.cong proj₂ >

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
