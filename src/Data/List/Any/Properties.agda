------------------------------------------------------------------------
-- Properties relating Any to various list functions
------------------------------------------------------------------------

module Data.List.Any.Properties where

open import Category.Monad
open import Data.Bool
open import Data.Bool.Properties
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (module Equivalent)
open import Function.Inverse using (_⇿_)
open import Data.List as List
open RawMonad List.monad
open import Data.List.Any as Any using (Any; here; there)
open import Data.Product hiding (map)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Unary using (_⟨×⟩_; _⟨→⟩_) renaming (_⊆_ to _⋐_)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; inspect; _with-≡_)

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

map⇿ : ∀ {A B} {P : B → Set} {f : A → B} {xs} →
        Any (P ∘ f) xs ⇿ Any P (map f xs)
map⇿ {P = P} = record
  { to         = P.→-to-⟶ $ map⁺ {P = P}
  ; from       = P.→-to-⟶ map⁻
  ; inverse-of = record
    { left-inverse-of  = map⁻∘map⁺ P
    ; right-inverse-of = map⁺∘map⁻
    }
  }

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

++⇿ : ∀ {A} {P : A → Set} {xs ys} →
      (Any P xs ⊎ Any P ys) ⇿ Any P (xs ++ ys)
++⇿ {xs = xs} = record
  { to         = P.→-to-⟶ [ ++⁺ˡ , ++⁺ʳ xs ]′
  ; from       = P.→-to-⟶ $ ++⁻ xs
  ; inverse-of = record
    { left-inverse-of  = ++⁻∘++⁺ xs
    ; right-inverse-of = ++⁺∘++⁻ xs
    }
  }

-- _++_ is idempotent.

++-idempotent : ∀ {A} {P : A → Set} {xs} →
                Any P (xs ++ xs) → Any P xs
++-idempotent = [ id , id ]′ ∘ ++⁻ _

-- _++_ is commutative.

++-comm : ∀ {A} {P : A → Set} xs ys →
          Any P (xs ++ ys) → Any P (ys ++ xs)
++-comm xs ys = [ ++⁺ʳ ys , ++⁺ˡ ]′ ∘ ++⁻ xs

++-comm∘++-comm : ∀ {A} {P : A → Set} xs {ys} (p : Any P (xs ++ ys)) →
                  ++-comm ys xs (++-comm xs ys p) ≡ p
++-comm∘++-comm [] {ys} p
 rewrite ++⁻∘++⁺ ys {ys = []} (inj₁ p) = P.refl
++-comm∘++-comm {P = P} (x ∷ xs) {ys} (here p)
  rewrite ++⁻∘++⁺ {P = P} ys {ys = x ∷ xs} (inj₂ (here p)) = P.refl
++-comm∘++-comm (x ∷ xs)      (there p) with ++⁻ xs p | ++-comm∘++-comm xs p
++-comm∘++-comm (x ∷ xs) {ys} (there .([ ++⁺ʳ xs , ++⁺ˡ ]′ (++⁻ ys (++⁺ʳ ys p))))
  | inj₁ p | P.refl
  rewrite ++⁻∘++⁺ ys (inj₂                 p)
        | ++⁻∘++⁺ ys (inj₂ $ there {x = x} p) = P.refl
++-comm∘++-comm (x ∷ xs) {ys} (there .([ ++⁺ʳ xs , ++⁺ˡ ]′ (++⁻ ys (++⁺ˡ    p))))
  | inj₂ p | P.refl
  rewrite ++⁻∘++⁺ ys {ys =     xs} (inj₁ p)
        | ++⁻∘++⁺ ys {ys = x ∷ xs} (inj₁ p) = P.refl

++⇿++ : ∀ {A} {P : A → Set} xs ys →
        Any P (xs ++ ys) ⇿ Any P (ys ++ xs)
++⇿++ xs ys = record
  { to         = P.→-to-⟶ $ ++-comm xs ys
  ; from       = P.→-to-⟶ $ ++-comm ys xs
  ; inverse-of = record
    { left-inverse-of  = ++-comm∘++-comm xs
    ; right-inverse-of = ++-comm∘++-comm ys
    }
  }

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

return⁻∘return⁺ : ∀ {A} (P : A → Set) {x} (p : P x) →
                  return⁻ {P = P} (return⁺ p) ≡ p
return⁻∘return⁺ P p = refl

return⇿ : ∀ {A} {P : A → Set} {x} →
          P x ⇿ Any P (return x)
return⇿ {P = P} = record
  { to         = P.→-to-⟶ return⁺
  ; from       = P.→-to-⟶ return⁻
  ; inverse-of = record
    { left-inverse-of  = return⁻∘return⁺ P
    ; right-inverse-of = return⁺∘return⁻
    }
  }

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

concat⇿ : ∀ {A} {P : A → Set} {xss} →
          Any (Any P) xss ⇿ Any P (concat xss)
concat⇿ {xss = xss} = record
  { to         = P.→-to-⟶ concat⁺
  ; from       = P.→-to-⟶ $ concat⁻ xss
  ; inverse-of = record
    { left-inverse-of  = concat⁻∘concat⁺
    ; right-inverse-of = concat⁺∘concat⁻ xss
    }
  }

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

>>=⇿ : ∀ {A B P xs} {f : A → List B} →
       Any (Any P ∘ f) xs ⇿ Any P (xs >>= f)
>>=⇿ {xs = xs} = record
  { to         = P.→-to-⟶ >>=⁺
  ; from       = P.→-to-⟶ $ >>=⁻ xs
  ; inverse-of = record
    { left-inverse-of  = >>=⁻∘>>=⁺
    ; right-inverse-of = >>=⁺∘>>=⁻ xs
    }
  }

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

⊛⁻∘⊛⁺ : ∀ {A B} (P : B → Set) {fs : List (A → B)} {xs}
        (p : Any (λ f → Any (P ∘ f) xs) fs) →
        ⊛⁻ {P = P} fs xs (⊛⁺ p) ≡ p
⊛⁻∘⊛⁺ P {fs} {xs} p =
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

⊛⇿ : ∀ {A B P} {fs : List (A → B)} {xs} →
     Any (λ f → Any (P ∘ f) xs) fs ⇿ Any P (fs ⊛ xs)
⊛⇿ {P = P} {fs} {xs} = record
  { to         = P.→-to-⟶ $ ⊛⁺ {P = P}
  ; from       = P.→-to-⟶ $ ⊛⁻ fs xs
  ; inverse-of = record
    { left-inverse-of  = ⊛⁻∘⊛⁺ P
    ; right-inverse-of = ⊛⁺∘⊛⁻ fs xs
    }
  }

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
any⁺ p (here  px)          = Equivalent.from T-∨ ⟨$⟩ inj₁ px
any⁺ p (there {x = x} pxs) with p x
... | true  = _
... | false = any⁺ p pxs

any⁻ : ∀ {A} (p : A → Bool) xs →
       T (any p xs) → Any (T ∘ p) xs
any⁻ p []       ()
any⁻ p (x ∷ xs) px∷xs with inspect (p x)
any⁻ p (x ∷ xs) px∷xs | true  with-≡ eq = here (Equivalent.from T-≡ ⟨$⟩
                                                  eq)
any⁻ p (x ∷ xs) px∷xs | false with-≡ eq with p x
any⁻ p (x ∷ xs) pxs   | false with-≡ refl | .false =
  there (any⁻ p xs pxs)
