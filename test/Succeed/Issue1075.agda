-- 2014-03-06 Andreas, Reported by Fabien Renaud

-- This is a larger example for the termination checker, to test performance.
-- In 2014-02-X, it exhausted the heap.

-- 2013-03-17
-- The termination checker now rejects this code instead of crashing.
-- I do not know whether it is supposed to terminate.

{-# OPTIONS --allow-unsolved-metas #-}

-- {-# OPTIONS -v term.matrices:40 #-}

module Issue1075 where

open import Common.Prelude renaming (Nat to ℕ) hiding (map; length)
open import Common.Product
open import Common.Sum
open import Common.Equality


[_] : ∀{A : Set} → A → List A
[ x ] = x ∷ []

map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr c n []       = n
foldr c n (x ∷ xs) = c x (foldr c n xs)

length : ∀ {A} → List A → ℕ
length = foldr (λ _ → suc) 0

postulate
  _∈_ : {A : Set} → A → List A → Set
  _⊆_ : {A : Set} → List A → List A → Set

infixr 5 _∷_

data All {A : Set}
         (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

_⋐_ : ∀{A} (P Q : A → Set) → Set
P ⋐ Q = ∀{x} → P x → Q x

map-all : ∀ {A : Set} {P : A → Set} {Q : A → Set} →
      P ⋐ Q → All P ⋐ All Q
map-all g []         = []
map-all g (px ∷ pxs) = g px ∷ map-all g pxs

-- Propositions and polarity

data Polarity : Set where
  ⁺ : Polarity
  ⁻ : Polarity

data Type : Polarity → Set where
  a : (Q : String) (⁼ : Polarity) → Type ⁼
  --
  ↓ : (A : Type ⁻) → Type ⁺
  ⊥⁺ : Type ⁺
  _∨_ : (A B : Type ⁺) → Type ⁺
  ⊤⁺ : Type ⁺
  _∧⁺_ : (A B : Type ⁺) → Type ⁺
  --
  ↑ : (A : Type ⁺) → Type ⁻
  _⊃_ : (A : Type ⁺) (B : Type ⁻) → Type ⁻
  ⊤⁻ : Type ⁻
  _∧⁻_ : (A B : Type ⁻) → Type ⁻


-- Judgmental infrastructure

data Conc : Set where
  Inv  : (A : Type ⁻) → Conc
  True : (A : Type ⁺) → Conc
  Susp : (A : Type ⁻) → Conc





stable : Conc → Set
stable (Inv A) = ⊥
stable (True A) = ⊤
stable (Susp A) = ⊤

suspnormal : Conc → Set
suspnormal (Inv A) = ⊤
suspnormal (True A) = ⊤
suspnormal (Susp (a Q .⁻)) = ⊤
suspnormal (Susp (↑ A)) = ⊥
suspnormal (Susp (A ⊃ A₁)) = ⊥
suspnormal (Susp ⊤⁻) = ⊥
suspnormal (Susp (A ∧⁻ A₁)) = ⊥

suspstable : Conc -> Set
suspstable U = stable U × suspnormal U

data Hyp : Set where
  HSusp : (A : Type ⁺) → Hyp
  Pers : (A : Type ⁻) → Hyp

Ctx = List Hyp


hsusp-inj : ∀{x y} → HSusp x ≡ HSusp y → x ≡ y
hsusp-inj refl = refl



{- Suspension normality: all suspended propositions are atomic -}
suspnormalΓ : Ctx → Set
suspnormalΓ Γ = ∀{A} → HSusp A {-Membership-≡.-}∈ Γ → ∃ λ Q → A ≡ (a Q ⁺)

postulate
  conssusp   : ∀{Γ Q} → suspnormalΓ Γ → suspnormalΓ ((HSusp (a Q ⁺)) ∷ Γ)
  conspers   : ∀{Γ A} → suspnormalΓ Γ → suspnormalΓ ((Pers A) ∷ Γ)
  fromctx    : ∀{A B Γ} (Γ' : Ctx) → B ∈ (Γ' ++ A ∷ Γ) → (A ≡ B) ⊎ (B ∈ (Γ' ++ Γ))
  fromctxGen : ∀{A} {Γ : Ctx} → (Γ' : Ctx) → (L : Ctx) → A ∈ (Γ' ++ L ++ Γ) → (A ∈ L) ⊎ (A ∈ (Γ' ++ Γ))


-- Sequent calculus

data SeqForm : Set where
  Rfoc : (A : Type ⁺) → SeqForm
  Left : (L : List (Type ⁺) ⊎ Type ⁻) (U : Conc) → SeqForm

suspnormalF : SeqForm → Set
suspnormalF (Rfoc A) = ⊤
suspnormalF (Left L U) = suspnormal U

data Exp (Γ : Ctx) : SeqForm → Set

Value : (Γ : Ctx) → Type ⁺ → Set
Value Γ A = Exp Γ (Rfoc A)

Term : (Γ : Ctx) → List (Type ⁺) → Conc → Set
Term Γ Ω U = Exp Γ (Left (inj₁ Ω) U)

Spine : (Γ : Ctx) (A : Type ⁻) (U : Conc) → Set
Spine Γ A U = Exp Γ (Left (inj₂ A) U)

data Exp Γ where

  -- Values
  id⁺ : ∀{A}
    (v : HSusp A ∈ Γ)
    → Value Γ A
  ↓R : ∀{A}
    (N : Term Γ [] (Inv A))
    → Value Γ (↓ A)
  ∨R₁ : ∀{A B}
    (V : Value Γ A)
    → Value Γ (A ∨ B)
  ∨R₂ : ∀{A B}
    (V : Value Γ B)
    → Value Γ (A ∨ B)
  ⊤⁺R : Value Γ ⊤⁺
  ∧⁺R : ∀{A B}
    (V₁ : Value Γ A)
    (V₂ : Value Γ B)
    → Value Γ (A ∧⁺ B)

  -- Terms
  focR : ∀{A}
    (V : Value Γ A)
    → Term Γ [] (True A)
  focL : ∀{A U}
    (pf : stable U)
    (x : Pers A ∈ Γ)
    (Sp : Spine Γ A U)
    → Term Γ [] U
  η⁺ : ∀{Q Ω U}
    (N : Term (HSusp (a Q ⁺) ∷ Γ) Ω U)
    → Term Γ (a Q ⁺ ∷ Ω) U
  ↓L : ∀{A Ω U}
    (N : Term (Pers A ∷ Γ) Ω U)
    → Term Γ (↓ A ∷ Ω) U
  ⊥L : ∀{U Ω}
    → Term Γ (⊥⁺ ∷ Ω) U
  ∨L : ∀{A B Ω U}
    (N₁ : Term Γ (A ∷ Ω) U)
    (N₂ : Term Γ (B ∷ Ω) U)
    → Term Γ ((A ∨ B) ∷ Ω) U
  ⊤⁺L : ∀{U Ω}
    (N : Term Γ Ω U)
    → Term Γ (⊤⁺ ∷ Ω) U
  ∧⁺L : ∀{U Ω A B}
    (N : Term Γ (A ∷ B ∷ Ω) U)
    → Term Γ ((A ∧⁺ B) ∷ Ω) U
  η⁻ : ∀{Q}
    (N : Term Γ [] (Susp (a Q ⁻)))
    → Term Γ [] (Inv (a Q ⁻))
  ↑R : ∀{A}
    (N : Term Γ [] (True A))
    → Term Γ [] (Inv (↑ A))
  ⊃R : ∀{A B}
    (N : Term Γ [ A ] (Inv B))
    → Term Γ [] (Inv (A ⊃ B))
  ⊤⁻R : Term Γ [] (Inv ⊤⁻)
  ∧⁻R : ∀{A B}
    (N₁ : Term Γ [] (Inv A))
    (N₂ : Term Γ [] (Inv B))
    → Term Γ [] (Inv (A ∧⁻ B))

  -- Spines
  id⁻ : ∀{A}
    → Spine Γ A (Susp A)
  ↑L : ∀{A U}
    (N : Term Γ [ A ] U)
    → Spine Γ (↑ A) U
  ⊃L : ∀{A B U}
    (V : Value Γ A)
    (Sp : Spine Γ B U)
    → Spine Γ (A ⊃ B) U
  ∧⁻L₁ : ∀{A B U}
    (Sp : Spine Γ A U)
    → Spine Γ (A ∧⁻ B) U
  ∧⁻L₂ : ∀{A B U}
    (Sp : Spine Γ B U)
    → Spine Γ (A ∧⁻ B) U

-- Weakening
postulate
  sub-cons-congr : ∀{A : Set} {x : A} {xs ys : List A}
      → xs ⊆ ys
      → (x ∷ xs) ⊆ (x ∷ ys)

  sub-wkex : ∀{A : Set} {x y : A} {xs ys : List A}
    → (x ∷ xs) ⊆ (x ∷ y ∷ xs)

  sub-cntr : ∀{A : Set} {x : A}
       → (xs : List A)
       → x ∈ xs
       → (x ∷ xs) ⊆ xs

  wk : ∀{Γ Γ' Form} → Γ ⊆ Γ' → Exp Γ Form → Exp Γ' Form
  wken : ∀{Γ A Form} → Exp Γ Form → Exp (A ∷ Γ) Form

wken-all-rfoc : ∀{Γ' Γ xs B}
  → All (λ A → Exp (Γ' ++ Γ) (Rfoc A)) xs
  → All (λ A → Exp (B ∷ (Γ' ++ Γ)) (Rfoc A)) xs
wken-all-rfoc [] = []
wken-all-rfoc (px ∷ All) = map-all (\x → wken x) (px ∷ All)


wken-all-inv : ∀{Γ' Γ Ω xs B}
  → All (λ A → Exp (Γ' ++ Γ) (Left (inj₁ Ω) (Inv A))) xs
  → All (λ A → Exp (B ∷ (Γ' ++ Γ)) (Left (inj₁ Ω) (Inv A))) xs
wken-all-inv [] = []
wken-all-inv (px ∷ All) = map-all (\x → wken x) (px ∷ All)

postulate
  wkex : ∀{Γ A B Form} → Exp (A ∷ Γ) Form → Exp (A ∷ B ∷ Γ) Form
  wkex2 : ∀{Γ A B C Form} → Exp (A ∷ B ∷ Γ) Form → Exp (A ∷ B ∷ C ∷ Γ) Form

cntr : ∀{A Form} → (Γ : Ctx) → A ∈ Γ → Exp (A ∷ Γ) Form → Exp Γ Form
cntr Γ In Exp = wk (sub-cntr Γ In) Exp

postulate

  exch-cons : ∀{Γ Γ' LA C x} → Term (x ∷ Γ ++ Γ') LA C → Term (Γ ++ x ∷ Γ') LA C

  subst⁺ :
    ∀{Γ Form}
    → (Γ' : Ctx)
    → (LAi : List (Type ⁺))
    → All (\x → Value (Γ' ++ Γ) x) LAi
    → Exp (Γ' ++ map (\x → HSusp x) (LAi) ++ Γ) Form
    → Exp (Γ' ++ Γ) Form

  subst⁻ : ∀{Γ A L U}
    → stable U
    → Exp Γ (Left L (Susp A))
    → Spine Γ A U
    → Exp Γ (Left L U)

cut⁺ : ∀{U Γ Ω}
  → suspnormalΓ Γ
  → suspnormal U
  → (LAi : List (Type ⁺))
  → All (\x → Value Γ x) LAi
  → Term Γ (LAi ++ Ω) U
  → Term Γ Ω U

cut⁻ : ∀{U Γ N}
  → suspnormalΓ Γ
  → suspstable U
  → (LA : List (Type ⁻))
  → (length LA ≡ suc N)
  → All (\x → Term Γ [] (Inv x)) LA
  → All (\x → Spine Γ x U) LA
  → Term Γ [] U

rsubst+  : ∀{Ω Γ Form} (Γ' : Ctx)
  → suspnormalΓ (Γ' ++ Γ)
  → suspnormal Form
  → (LA+ : List (Type ⁺))
  → (LA- : List (Type ⁻))
  → All (\x →  Term (Γ' ++ Γ) [] (Inv x)) LA-
  → All (\x → Value Γ x) LA+
  → Term (Γ' ++ (map (\x → Pers x) LA-) ++ Γ) (LA+ ++ Ω) Form
  → Term (Γ' ++ Γ) Ω  Form

postulate rsubst-v : ∀{Γ Form} (Γ' : Ctx)   → suspnormalΓ (Γ' ++ Γ)  → suspnormalF Form  → (LA- : List (Type ⁻))  → All (\x →  Term (Γ' ++ Γ) [] (Inv x)) LA-  → Exp (Γ' ++ (map (\x → Pers x) LA-) ++ Γ) Form  → Exp (Γ' ++ Γ) Form


lsubst : ∀{Γ U L A}
  → suspnormalΓ Γ
  → suspstable U
  → Exp Γ (Left L (True A))
  → Term Γ [ A ] U
  → Exp Γ (Left L U)




-- -- Positive principal substitution

cut⁺ pfΓ pf [] Values T = T

cut⁺ pfΓ pf (z ∷ LA) ((id⁺ v) ∷ Values) N with (pfΓ v)
cut⁺ pfΓ pf (.(a A ⁺) ∷ LA) (id⁺ v ∷ Values) (η⁺ N) | A , refl =
  subst⁺ [] (a A ⁺ ∷ []) (id⁺ v ∷ []) (cut⁺ (conssusp pfΓ) pf LA (wken-all-rfoc {[]} Values) N)
cut⁺ {U} {Γ} {Ω} pfΓ pf (.(↓ A) ∷ LA) (↓R N ∷ Values) (↓L {A} N') =
  rsubst+ [] pfΓ pf LA (A ∷ []) (N ∷ []) Values N'
  -- rsubst+ [] pfΓ pf N (cut⁺ (conspers pfΓ) pf LA (wken-all-rfoc {[]} Values) N₁)
cut⁺ pfΓ pf (.(A ∨ B) ∷ LA) (∨R₁ V ∷ Values) (∨L {A} {B} N₁ N₂) = cut⁺ pfΓ pf (A ∷ LA) (V ∷ Values) N₁
cut⁺ pfΓ pf (.(A ∨ B) ∷ LA) (∨R₂ V ∷ Values) (∨L {A} {B} N₁ N₂) =  cut⁺ pfΓ pf (B ∷ LA) (V ∷ Values) N₂
cut⁺ pfΓ pf (.⊤⁺ ∷ LA) (px ∷ Values) (⊤⁺L N) = cut⁺ pfΓ pf LA Values N
cut⁺ pfΓ pf ((A ∧⁺ B) ∷ LA) (∧⁺R V₁ V₂ ∷ Values) (∧⁺L N) = cut⁺ pfΓ pf (B ∷ LA) (V₂ ∷ Values) (cut⁺ pfΓ pf ((A ∷ [])) (V₁ ∷ [])  N)

-- -- Negative principle substitution


cut⁻ pfΓ pf [] () LExp LExp'
cut⁻ pfΓ pf (_ ∷ LA) LL (focL () x Sp ∷ LExp) (px₁ ∷ LExp')

cut⁻ pfΓ pf (a Q .⁻ ∷ LA) LL (η⁻ N₁ ∷ LExp) (id⁻ ∷ LExp') = N₁

cut⁻ pfΓ (proj₁ , ()) (⊤⁻ ∷ LA) LL (⊤⁻R ∷ LExp) (id⁻ ∷ LExp')
cut⁻ pfΓ (proj₁ , ()) (↑ x ∷ LA) LL (↑R N₁ ∷ LExp) (id⁻ ∷ LExp')
cut⁻ pfΓ (proj₁ , ()) ((x ⊃ x₁) ∷ LA) LL (⊃R N₁ ∷ LExp) (id⁻ ∷ LExp')
cut⁻ pfΓ (proj₁ , ()) ((x ∧⁻ x₁) ∷ LA) LL (∧⁻R N₁ N₂ ∷ LExp) (id⁻ ∷ LExp')

cut⁻ pfΓ pf (↑ x ∷ LA) LL (↑R N₁ ∷ LExp) (↑L N₂ ∷ LExp') = lsubst pfΓ pf N₁ N₂

cut⁻ pfΓ pf ((x ⊃ x₁) ∷ LA) refl (⊃R N₁ ∷ LExp) (⊃L V Sp ∷ LExp') =
  cut⁻ pfΓ pf (x₁ ∷ LA) refl ((cut⁺ pfΓ _ (x ∷ []) (V ∷ []) N₁) ∷ LExp) (Sp ∷ LExp')

cut⁻ pfΓ pf ((x ∧⁻ x₁) ∷ LA) refl (∧⁻R N₁ N₂ ∷ LExp) (∧⁻L₁ Sp ∷ LExp') =
  cut⁻ pfΓ pf (x ∷ LA) refl (N₁ ∷ LExp) (Sp ∷ LExp')

cut⁻ pfΓ pf ((x ∧⁻ x₁) ∷ LA) LL (∧⁻R N₁ N₂ ∷ LExp) (∧⁻L₂ Sp ∷ LExp') =
  cut⁻ pfΓ pf (x₁ ∷ LA) refl (N₂ ∷ LExp) (Sp ∷ LExp')

-- helper : ∀{Γ LA- A} →
--   All (λ x₂ → Exp (Γ) (Left (inj₁ []) (Inv x₂))) LA-
--   → Any (_≡_ (Pers A)) (map Pers LA-)
--   → All (λ x₂ → Exp (Γ) (Left (inj₁ []) (Inv x₂))) (A ∷ [])
-- helper [] ()
-- helper (px ∷ L) (here refl) = px ∷ []
-- helper (px ∷ L) (there In) = helper L In

rsubst+ Γ' pfΓ pf [] LA- LT [] (focR V) = focR (rsubst-v Γ' pfΓ _ LA- LT V )
rsubst+ Γ' pfΓ pf [] LA- LT [] (focL pf₁ x Sp) with fromctxGen Γ' (map Pers LA-) x
rsubst+ Γ' pfΓ pf [] LA- LT [] (focL {A} pf₁ x Sp) | inj₁ x₁ =
  cut⁻ pfΓ (pf₁ , pf) (A ∷ []) refl {!(helper LT x₁)!} ((rsubst-v Γ' pfΓ pf LA- LT Sp) ∷ [])
rsubst+ Γ' pfΓ pf [] LA- LT [] (focL pf₁ x Sp) | inj₂ y =
  focL pf₁ y (rsubst-v Γ' pfΓ pf LA- LT Sp )
rsubst+ Γ' pfΓ pf [] LA- LT [] (η⁺ N) =
  η⁺ (rsubst-v (_ ∷ Γ' ) (conssusp pfΓ) pf LA- (wken-all-inv {[]} LT) N )
rsubst+ Γ' pfΓ pf [] LA- LT [] (↓L N) =
  ↓L (rsubst-v (_ ∷ Γ' ) (conspers pfΓ) pf LA- (wken-all-inv {[]} LT) N )
rsubst+ Γ' pfΓ pf [] LA- LT [] ⊥L = ⊥L
rsubst+ Γ' pfΓ pf [] LA- LT [] (∨L N₁ N₂) =
  ∨L (rsubst+ Γ' pfΓ pf [] LA- LT [] N₁) (rsubst+ Γ' pfΓ pf [] LA- LT [] N₂)
rsubst+ Γ' pfΓ pf [] LA- LT [] (⊤⁺L N) = ⊤⁺L (rsubst+ Γ' pfΓ pf [] LA- LT [] N )
rsubst+ Γ' pfΓ pf [] LA- LT [] (∧⁺L N) = ∧⁺L (rsubst+  Γ' pfΓ pf [] LA- LT [] N)
rsubst+ Γ' pfΓ pf [] LA- LT [] (η⁻ N) = η⁻ (rsubst+  Γ' pfΓ pf [] LA- LT [] N)
rsubst+ Γ' pfΓ pf [] LA- LT [] (↑R N) = ↑R (rsubst+  Γ' pfΓ pf [] LA- LT [] N)
rsubst+ Γ' pfΓ pf [] LA- LT [] (⊃R N) = ⊃R (rsubst+  Γ' pfΓ pf [] LA- LT [] N)
rsubst+ Γ' pfΓ pf [] LA- LT [] ⊤⁻R = ⊤⁻R
rsubst+ Γ' pfΓ pf [] LA- LT [] (∧⁻R N₁ N₂) =
  ∧⁻R (rsubst+  Γ' pfΓ pf [] LA- LT [] N₁) (rsubst+  Γ' pfΓ pf [] LA- LT [] N₂)


-- rsubst+ Γ' pfΓ pf (↓ x ∷ LA+) LA- LT (id⁺ v ∷ Values) (↓L N) with (pfΓ (++ʳ Γ' v))
-- ... | proj₁ , ()

-- ------------
-- -- Part which requires a list for negative types
-- rsubst+ {Ω} {Γ} Γ' pfΓ pf (a Q .⁺ ∷ LA+) LA- LT (id⁺ v ∷ Values) (η⁺ N) =
--   rsubst+ Γ' pfΓ pf LA+ LA- (LT ) Values
--           (cntr (Γ' ++ map Pers LA- ++ Γ) (++ʳ Γ' (++ʳ (map Pers LA-) v) ) N)


-- rsubst+ {Ω} {Γ} Γ' pfΓ pf (↓ x ∷ LA+) LA- LT (↓R N ∷ Values) (↓L N₁) =
--   rsubst+ Γ' pfΓ pf LA+ (x ∷ LA-) ((wk (λ x₂ → ++ʳ Γ' x₂) N) ∷ LT)  Values (exch-cons {Γ'} {map Pers LA- ++ Γ} N₁)
--------------
-- rsubst+ Γ' pfΓ pf (⊥⁺ ∷ LA+) LA- LT (id⁺ v ∷ Values) ⊥L with (pfΓ (++ʳ Γ' v))
-- ... | proj₁ , ()
-- rsubst+ Γ' pfΓ pf (x ∨ x₁ ∷ LA+) LA- LT (id⁺ v ∷ Values) (∨L N₁ N₂)  with (pfΓ (++ʳ Γ' v))
-- ... | proj₁ , ()
rsubst+ Γ' pfΓ pf ((x ∨ x₁) ∷ LA+) LA- LT (∨R₁ V ∷ Values) (∨L N₁ N₂) = rsubst+ Γ' pfΓ pf (x ∷ LA+) LA- LT (V ∷ Values) N₁
rsubst+ Γ' pfΓ pf ((x ∨ x₁) ∷ LA+) LA- LT (∨R₂ V ∷ Values) (∨L N₁ N₂) = rsubst+ Γ' pfΓ pf (x₁ ∷ LA+) LA- LT (V ∷ Values) N₂
rsubst+ Γ' pfΓ pf (⊤⁺ ∷ LA+) LA- LT (_ ∷ Values) (⊤⁺L N) =  rsubst+ Γ' pfΓ pf LA+ LA- LT Values N
-- rsubst+ Γ' pfΓ pf (x ∧⁺ x₁ ∷ LA+) LA- LT (id⁺ v ∷ Values) (∧⁺L N) with (pfΓ (++ʳ Γ' v))
-- ... | proj₁ , ()
rsubst+ Γ' pfΓ pf ((x ∧⁺ x₁) ∷ LA+) LA- LT (∧⁺R V₁ V₂ ∷ Values) (∧⁺L N) =
  rsubst+ Γ' pfΓ pf (x ∷ x₁ ∷ LA+) LA- LT (V₁ ∷ V₂ ∷ Values) N
rsubst+ {_} {_} {_} _ _ _ _ _ _ _ _ = ?



-- -- -- Substitution out of terms
lsubst pfΓ pf (focR {A} V) N = cut⁺ pfΓ (proj₂ pf) (A ∷ []) (V ∷ []) N
lsubst pfΓ pf (focL pf' x Sp) N = focL (proj₁ pf) x (lsubst pfΓ pf Sp N)
lsubst pfΓ pf (η⁺ M) N = η⁺ (lsubst (conssusp pfΓ) pf M (wken N))
lsubst pfΓ pf (↓L M) N = ↓L (lsubst (conspers pfΓ) pf M (wken N))
lsubst pfΓ pf ⊥L M = ⊥L
lsubst pfΓ pf (∨L M₁ M₂) N = ∨L (lsubst pfΓ pf M₁ N) (lsubst pfΓ pf M₂ N)
lsubst pfΓ pf (⊤⁺L M) N = ⊤⁺L (lsubst pfΓ pf M N)
lsubst pfΓ pf (∧⁺L M) N = ∧⁺L (lsubst pfΓ pf M N)

-- Substitution of of spines
lsubst pfΓ pf (↑L M) N = ↑L (lsubst pfΓ pf M N)
lsubst pfΓ pf (⊃L V Sp) N = ⊃L V (lsubst pfΓ pf Sp N)
lsubst pfΓ pf (∧⁻L₁ Sp) N = ∧⁻L₁ (lsubst pfΓ pf Sp N)
lsubst pfΓ pf (∧⁻L₂ Sp) N = ∧⁻L₂ (lsubst pfΓ pf Sp N)
