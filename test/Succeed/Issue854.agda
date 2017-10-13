-- 2013-06-15 Andreas, issue reported by Stevan Andjelkovic
module Issue854 where

infixr 1 _⊎_
infixr 2 _×_
infixr 4 _,_
infix 4 _≡_

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

record ⊤ : Set where
  constructor tt

data Bool : Set where
  true false : Bool

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : (x : A) → Maybe A

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

[_,_] : ∀ {A : Set} {B : Set} {C : A ⊎ B → Set} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

[_,_]₁ : ∀ {A : Set} {B : Set} {C : A ⊎ B → Set₁} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ]₁ (inj₁ x) = f x
[ f , g ]₁ (inj₂ y) = g y

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

uncurry₁ : {A : Set} {B : A → Set} {C : Σ A B → Set₁} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry₁ f (x , y) = f x y

------------------------------------------------------------------------

infix 5 _◃_
infixr 1 _⊎C_
infixr 2 _×C_

record Container : Set₁ where
  constructor _◃_
  field
    Shape     : Set
    Position  : Shape → Set

open Container public

⟦_⟧ : Container → (Set → Set)
⟦ S ◃ P ⟧ X = Σ S λ s → P s → X

idC : Container
idC = ⊤ ◃ λ _ → ⊤

constC : Set → Container
constC X = X ◃ λ _ → ⊥

𝟘 = constC ⊥
𝟙 = constC ⊤

_⊎C_ : Container → Container → Container
S ◃ P ⊎C S′ ◃ P′ = (S ⊎ S′) ◃ [ P , P′ ]₁

_×C_ : Container → Container → Container
S ◃ P ×C S′ ◃ P′ = (S × S′) ◃ uncurry₁ (λ s s′ → P s ⊎ P′ s′)

data μ (C : Container) : Set where
  ⟨_⟩ : ⟦ C ⟧ (μ C) → μ C


_⋆C_ : Container → Set → Container
C ⋆C X = constC X ⊎C C

_⋆_ : Container → Set → Set
C ⋆ X = μ (C ⋆C X)

AlgIter : Container → Set → Set
AlgIter C X = ⟦ C ⟧ X → X

iter : ∀ {C X} → AlgIter C X → μ C → X
iter φ ⟨ s , k ⟩ = φ (s , λ p → iter φ (k p))

AlgRec : Container → Set → Set
AlgRec C X = ⟦ C ⟧ (μ C × X) → X

rec : ∀ {C X} → AlgRec C X → μ C → X
rec φ ⟨ s , k ⟩ = φ (s , λ p → (k p , rec φ (k p)))

return : ∀ {C X} → X → C ⋆ X
return x = ⟨ inj₁ x , ⊥-elim ⟩

act : ∀ {C X} → ⟦ C ⟧ (C ⋆ X) → C ⋆ X
act (s , k) = ⟨ inj₂ s , k ⟩

_>>=_ : ∀ {C X Y} → C ⋆ X → (X → C ⋆ Y) → C ⋆ Y
_>>=_ {C}{X}{Y} m k = iter φ m
  where
  φ : AlgIter (C ⋆C X) (C ⋆ Y)
  φ (inj₁ x  , _)  = k x
  φ (inj₂ s  , k)  = act (s , k)

------------------------------------------------------------------------

_↠_ : Set → Set → Container
I ↠ O = I ◃ λ _ → O

State : Set → Container
State S  =   (⊤ ↠ S)   -- get
         ⊎C  (S ↠ ⊤)   -- put

get : ∀ {S} → State S ⋆ S
get = act (inj₁ tt , return)

put : ∀ {S} → S → State S ⋆ ⊤
put s = act (inj₂ s , return)

Homo : Container → Set → Set → Container → Set → Set
Homo Σ X I Σ′ Y = AlgRec (Σ ⋆C X) (I → Σ′ ⋆ Y)

Pseudohomo : Container → Set → Set → Container → Set → Set
Pseudohomo Σ X I Σ′ Y =
    ⟦ Σ ⋆C X ⟧ (((Σ ⊎C Σ′) ⋆ X) × (I → Σ′ ⋆ Y)) → I → Σ′ ⋆ Y

state : ∀ {Σ S X} → Pseudohomo (State S) X S Σ (X × S)
state (inj₁ x         , _)  = λ s  → return (x , s)  -- return
state (inj₂ (inj₁ _)  , k)  = λ s  → proj₂ (k s) s   -- get
state (inj₂ (inj₂ s)  , k)  = λ _  → proj₂ (k tt) s  -- put

Abort : Container
Abort = ⊤ ↠ ⊥

aborting : ∀ {X} → Abort ⋆ X
aborting = act (tt , ⊥-elim)

abort : ∀ {Σ X} → Pseudohomo Abort X ⊤ Σ (Maybe X)
abort (inj₁ x  , _) _ = return (just x)  -- return
abort (inj₂ _  , _) _ = return nothing   -- abort

------------------------------------------------------------------------

record _⇒_ (C C′ : Container) : Set where
  field
    shape    : Shape C → Shape C′
    position : ∀ {s} → Position C′ (shape s) → Position C s

open _⇒_ public

idMorph : ∀ {C} → C ⇒ C
idMorph = record { shape = λ s → s; position = λ p → p }

inlMorph : ∀ {C C′ : Container} → C ⇒ (C ⊎C C′)
inlMorph = record
  { shape    = inj₁
  ; position = λ p → p
  }

swapMorph : ∀ {C C′} → (C ⊎C C′) ⇒ (C′ ⊎C C)
swapMorph {C}{C′}= record
  { shape    = sh
  ; position = λ {s} p → pos {s} p
  }
  where
  sh : Shape C ⊎ Shape C′ → Shape C′ ⊎ Shape C
  sh (inj₁ s)  = inj₂ s
  sh (inj₂ s′) = inj₁ s′

  pos : ∀ {s} → Position (C′ ⊎C C) (sh s) → Position (C ⊎C C′) s
  pos {inj₁ s}  p  = p
  pos {inj₂ s′} p′ = p′

⟪_⟫ : ∀ {C C′ X} → C ⇒ C′ → ⟦ C ⟧ X → ⟦ C′ ⟧ X
⟪ m ⟫ xs = shape m (proj₁ xs) , λ p′ → proj₂ xs (position m p′)

⟪_⟫Homo : ∀ {C C′ X} → C ⇒ C′ → Homo C X ⊤ C′ X
⟪ m ⟫Homo (inj₁ x , _)  _ = return x
⟪ m ⟫Homo (inj₂ s , k)  _ =  let (s′ , k′) = ⟪ m ⟫ (s , k)
                             in  act (s′ , λ p′ → proj₂ (k′ p′) tt)

natural : ∀ {C C′ X} → C ⇒ C′ → C ⋆ X → C′ ⋆ X
natural f m = rec ⟪ f ⟫Homo m tt

inl : ∀ {C C′ X} → C ⋆ X → (C ⊎C C′) ⋆ X
inl = natural inlMorph

squeeze : ∀ {Σ Σ′ X} → ((Σ ⊎C Σ′) ⊎C Σ′) ⋆ X → (Σ ⊎C Σ′) ⋆ X
squeeze = natural m
  where
  m = record
    { shape    = [ (λ x → x) , inj₂ ]
    ; position = λ { {inj₁ x} p → p ; {inj₂ x} p → p}
    }

lift : ∀ {Σ Σ′ X Y I} → Pseudohomo Σ X I Σ′ Y →
         Pseudohomo (Σ ⊎C Σ′) X I Σ′ Y
lift φ (inj₁ x , _)          i = φ (inj₁ x , ⊥-elim) i
lift φ (inj₂ (inj₁ s) , k)   i = φ (inj₂ s , λ p →
                                     let (w , ih) = k p in squeeze w , ih) i
lift φ (inj₂ (inj₂ s′) , k′) i = act (s′ , λ p′ → proj₂ (k′ p′) i)

weaken : ∀ {Σ Σ′ Σ″ Σ‴ X Y I} → Homo Σ′ X I Σ″ Y →
           Σ ⇒ Σ′ → Σ″ ⇒ Σ‴ → Homo Σ X I Σ‴ Y
weaken {Σ}{Σ′}{Σ″}{Σ‴}{X}{Y} φ f g (s , k) i = w‴
  where
  w : Σ ⋆ X
  w = ⟨ s , (λ p → proj₁ (k p)) ⟩

  w′ : Σ′ ⋆ X
  w′ = natural f w

  w″ : Σ″ ⋆ Y
  w″ = rec φ w′ i

  w‴ : Σ‴ ⋆ Y
  w‴ = natural g w″

⌈_⌉Homo : ∀ {Σ Σ′ X Y I} → Pseudohomo Σ X I Σ′ Y → Homo Σ X I Σ′ Y
⌈ φ ⌉Homo (inj₁ x , _)  = φ (inj₁ x , ⊥-elim)
⌈ φ ⌉Homo (inj₂ s , k)  = φ (inj₂ s , λ p →  let (w , ih) = k p
                                             in  inl w , ih)

run : ∀ {Σ Σ′ Σ″ Σ‴ X Y I} → Pseudohomo Σ X I Σ′ Y →
        Σ″ ⇒ (Σ ⊎C Σ′) → Σ′ ⇒ Σ‴ →
        Σ″ ⋆ X → I → Σ‴ ⋆ Y
run φ p q = rec (weaken ⌈ lift φ ⌉Homo p q)

------------------------------------------------------------------------

prog : (State ℕ ⊎C Abort) ⋆ Bool
prog =
  ⟨ inj₂ (inj₁ (inj₁ tt)) ,       (λ n →   -- get          >>= λ n →
  ⟨ inj₂ (inj₁ (inj₂ (suc n))) ,  (λ _ →   -- put (suc n)
  ⟨ inj₂ (inj₂ tt) ,              (λ _ →   -- aborting
  return true) ⟩) ⟩) ⟩

progA : State ℕ ⋆ Maybe Bool
progA = run abort swapMorph idMorph prog tt

progS : ℕ → Abort ⋆ (Bool × ℕ)
progS = run state idMorph idMorph prog

progAS : ℕ → 𝟘 ⋆ (Maybe Bool × ℕ)
progAS = run state inlMorph idMorph progA

progSA : ℕ → 𝟘 ⋆ Maybe (Bool × ℕ)
progSA n = run abort inlMorph idMorph (progS n) tt

testSA : progSA zero ≡ return nothing
testSA = refl

testAS : progAS zero ≡ return (nothing , suc zero)
testAS = refl

-- The last statement seemed to make the type checker loop.
-- But it just created huge terms during the conversion check
-- and never finished.
-- These terms contained many projection redexes
-- (projection applied to record value).

-- After changing the strategy, such that these redexes are,
-- like beta-redexes, removed immediately in internal syntax,
-- the code checks instantaneously.
