-- Building some simple tactics using the reflected type checking monad.
module _ where

open import Common.Reflection
open import Common.Prelude hiding (_>>=_)
open import Common.Equality
open import Agda.Builtin.Sigma

-- Some helpers --

quotegoal : (Type → Tactic) → Tactic
quotegoal tac hole =
  inferType hole >>= λ goal →
  reduce goal >>= λ goal →
  tac goal hole

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

replicateTC : {A : Set} → Nat → TC A → TC (List A)
replicateTC zero m = returnTC []
replicateTC (suc n) m = m >>= λ x → replicateTC n m >>= λ xs → returnTC (x ∷ xs)

mapTC! : ∀ {A : Set} → (A → TC ⊤) → List A → TC ⊤
mapTC! f [] = returnTC _
mapTC! f (x ∷ xs) = f x >>= λ _ → mapTC! f xs

mapTC!r : ∀ {A} → (A → TC ⊤) → List A → TC ⊤
mapTC!r f [] = returnTC _
mapTC!r f (x ∷ xs) = mapTC! f xs >>= λ _ → f x

visibleArity : QName → TC Nat
visibleArity q = getType q >>= λ t → returnTC (typeArity t)
  where
    typeArity : Type → Nat
    typeArity (pi (arg (argInfo visible _) _) (abs _ b)) = suc (typeArity b)
    typeArity (pi _ (abs _ b)) = typeArity b
    typeArity _ = 0

newMeta! : TC Term
newMeta! = newMeta unknown

absurdLam : Term
absurdLam = extLam (absurdClause
                      (("()" , arg (argInfo visible relevant) unknown) ∷ [])
                      (arg (argInfo visible relevant) absurd ∷ [])
                   ∷ []) []

-- Simple assumption tactic --

assumption-tac : Nat → Nat → Tactic
assumption-tac x 0 _ = typeError (strErr "No assumption matched" ∷ [])
assumption-tac x (suc n) hole =
  catchTC (unify hole (var x []))
          (assumption-tac (suc x) n hole)

macro
  assumption : Tactic
  assumption hole = getContext >>= λ Γ → assumption-tac 0 (length Γ) hole

test-assumption : ∀ {A B : Set} → A → B → A
test-assumption x y = assumption

test-assumption₂ : ∀ {A B : Set} → A → B → _
test-assumption₂ x y = assumption  -- will pick y

-- Solving a goal using only constructors --

tryConstructors : Nat → List QName → Tactic

constructors-tac : Nat → Type → Tactic
constructors-tac zero _ _ = typeError (strErr "Search depth exhausted" ∷ [])
constructors-tac (suc n) (def d vs) hole =
  getDefinition d >>= λ def →
  case def of λ
  { (dataDef _ cs) → tryConstructors n cs hole
  ; _              → returnTC _ }
constructors-tac _ (pi a b) hole = give absurdLam hole
constructors-tac _ _ hole = returnTC _

tryConstructors n []       hole = typeError (strErr "No matching constructor term" ∷ [])
tryConstructors n (c ∷ cs) hole =
  visibleArity c >>= λ ar →
  catchTC (replicateTC ar newMeta! >>= λ vs →
           unify hole (con c (map (arg (argInfo visible relevant)) vs)) >>= λ _ →
           mapTC!r (quotegoal (constructors-tac n)) vs)
          (tryConstructors n cs hole)

macro
  constructors : Tactic
  constructors = quotegoal (constructors-tac 10)

data Any {A : Set} (P : A → Set) : List A → Set where
  zero : ∀ {x xs} → P x      → Any P (x ∷ xs)
  suc  : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

infix 1 _∈_
_∈_ : ∀ {A : Set} → A → List A → Set
x ∈ xs = Any (x ≡_) xs

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A

test₁ : 3 ∈ 1 ∷ 2 ∷ 3 ∷ []
test₁ = constructors

test₂ : Dec (2 + 3 ≡ 5)
test₂ = constructors

test₃ : Dec (2 + 2 ≡ 5)
test₃ = constructors

data Singleton (n : Nat) : Set where
  it : (m : Nat) → m ≡ n → Singleton n

test₄ : Singleton 5
test₄ = constructors -- this works because we solve goals right to left (picking refl before m)
