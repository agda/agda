\subsection{Examples}
\label{examples}

\AgdaHide{
\begin{code}

{-# OPTIONS --sized-types #-}

module Issue854.Examples where

open import Function.Base
open import Function.Inverse using (module Inverse)
open import Data.Unit
open import Data.Product
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Container.FreeMonad using (rawMonad)
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Binary.Pointwise hiding (refl)
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (xs⊆xs++ys)
open import Category.Monad

open import Issue854.Types
open import Issue854.Context
open import Issue854.WellTyped
open import Issue854.WellTypedSemantics
\end{code}
}

\begin{code}
′N : Sig
′N = (𝟙 , 𝟘) ∷ (𝟙 , 𝟙) ∷ []

N = μ ′N

ze : ∀ {Γ} → Γ ⊢^v _ ∶ N
ze = con (here refl) ⟨⟩ (𝟘-elim (var zero))

pattern su n = con (there (here refl)) ⟨⟩ n

#0 #1 #2 #3 #4 #5 : ∀ {Γ} → Γ ⊢^v _ ∶ N

#0 = ze
#1 = su #0
#2 = su #1
#3 = su #2
#4 = su #3
#5 = su #4

_⊙_ : ∀ {Γ Σ U V f a} → Γ ▻ U ⊢^v f ∶ V → Γ ⊢^c a ∶ Σ ⋆ U → Γ ⊢^c _ ∶ Σ ⋆ V
f ⊙ a = _to_ a (return f) id id

plus : ∀ {Γ Σ} → Γ ⊢^c _ ∶ N ⇒ N ⇒ Σ ⋆ N
plus = ƛ {-m-} ƛ {-n-} _⊢^c_∶_.iter φ (var {-m-} (suc zero))
  where
  φ : _ ⊢^cs _ ∶ Alg ′N (_ ⋆ N)
  φ =  ƛ ƛ return (var {-n-} (suc (suc zero))) ∷
       ƛ ƛ (su′ ⊙ ih) ∷
       []
    -- XXX: Not indented properly...
    where
    su′ : _ ▻ N ⊢^v _ ∶ N
    su′ = con (there (here refl)) ⟨⟩ (var (suc zero))

    ih : _ ⊢^c _ ∶ _ ⋆ N
    ih = force (var zero) · ⟨⟩

-- test-plus : ⟦ plus {[]}{[]} · #2 · #1 ⟧^c tt ≡ ⟦ return #3 ⟧^c tt
-- test-plus = refl

State : VType → Sig
State S = (𝟙 , S) ∷ (S , 𝟙) ∷ []

-- XXX: get : {m : True (𝟙 , S) ∈? Σ)} → Σ ⋆ S?

state^suc : ∀ {Γ} → Γ ⊢^c _ ∶ State N ⋆ 𝟙
state^suc {Γ} = _to_ (op get · ⟨⟩) (op put · su′) id id
  where
  get = here refl
  put = there (here refl)

  su′ : Γ ▻ N ⊢^v _ ∶ N
  su′ = con (there (here refl)) ⟨⟩ (var (suc zero))

state^Homo : ∀ {Γ Σ S X} → Γ ⊢^cs _ ∶ PHomo (State S) X S Σ (X ⊗ S)
state^Homo =
  ƛ ƛ ƛ (((π₂ (force (var (suc zero)) · var zero)) · var zero)) ∷
  ƛ ƛ ƛ ((π₂ (force (var (suc zero)) · ⟨⟩)) · var (suc (suc zero))) ∷
  ƛ ƛ return (var (suc zero) , var zero) ∷ []

ex-state : [] ⊢^c _ ∶ [] ⋆ (𝟙 ⊗ N)
ex-state = run {Σ′ = State N}{[]} state^Homo state^suc (xs⊆xs++ys _ _) id · #0

test-state : ⟦ ex-state ⟧^c tt ≡ ⟦ return (⟨⟩ , #1) ⟧^c tt
test-state = refl
\end{code}

The booleans.

\begin{code}
′𝟚  : Sig
′𝟚  = (𝟙 , 𝟘) ∷ (𝟙 , 𝟘) ∷ []
𝟚   = μ ′𝟚

tru fal : ∀ {Γ} → Γ ⊢^v _ ∶ 𝟚
tru  = con (here refl)          ⟨⟩ (𝟘-elim (var zero))
fal  = con (there (here refl))  ⟨⟩ (𝟘-elim (var zero))

cond : ∀ {Γ Σ V} → Γ ⊢^c _ ∶ 𝟚 ⇒ V ⇒ V ⇒ Σ ⋆ V
cond {Γ}{Σ}{T} = ƛ {-b-} ƛ {-t-} ƛ {-f-} iter φ
    (var {-b-} (suc (suc zero)))
  where
  φ : Γ ▻ 𝟚 ▻ T ▻ T ⊢^cs _ ∶ Alg ′𝟚 (Σ ⋆ T)
  φ =  ƛ ƛ return (var {-t-} (suc (suc (suc zero)))) ∷
       ƛ ƛ return (var {-f-} (suc (suc zero))) ∷ []

if : ∀ {Γ C} → Γ ⊢^c _ ∶ 𝟚 ⇒ ⁅ C ⁆ ⇒ ⁅ C ⁆ ⇒ C
if {Γ}{C} = ƛ {-b-} ƛ {-t-} ƛ {-f-} iter φ
    (var {-b-} (suc (suc zero)))
  where
  φ : Γ ▻ 𝟚 ▻ ⁅ C ⁆ ▻ ⁅ C ⁆ ⊢^cs _ ∶ Alg ′𝟚 C
  φ =  ƛ ƛ force (var {-t-} (suc (suc (suc zero)))) ∷
       ƛ ƛ force (var {-f-} (suc (suc zero))) ∷ []
\end{code}

\begin{code}
not : ∀ {Γ Σ} → Γ ⊢^c _ ∶ 𝟚 ⇒ Σ ⋆ 𝟚
not = ƛ (cond · var zero · fal · tru)
\end{code}

Possibly aborting computations.

\begin{code}
Abort : Sig
Abort = (𝟙 , 𝟘) ∷ []

aborting : ∀ {Γ V} → Γ ⊢^c _ ∶ Abort ⋆ V
aborting = _to_  (op (here refl) · ⟨⟩)
                 (return (𝟘-elim (var zero))) id id
\end{code}

\begin{code}
-- postulate
--   weaken^C : ∀ {Γ V C c} → Γ ⊢^c c ∶ C → Γ ▻ V ⊢^c c ∶ C
--
-- _<_·_>_ : ∀ {Γ Σ Σ′ Σ″ U V f a} → Γ ⊢^c f ∶ U ⇒ Σ ⋆ V → Σ ⊆ Σ″ → Σ′ ⊆ Σ″ →
--           Γ ⊢^c a ∶ Σ′ ⋆ U → Γ ⊢^c _ ∶ Σ″ ⋆ V
-- f < p · q > a = _to_ a (weaken^C f · var zero) q p
--
-- put-abort : ∀ {Γ S} → Γ ⊢^c _ ∶ (State S ++ Abort) ⋆ 𝟙
-- put-abort {S = S} = op put < xs⊆xs++ys · xs⊆ys++xs {xs = State S} > aborting
-- -- (aborting to (op put · var zero)) (inr′ {xs = State S}) inl′
--   where
--   put : (S , 𝟙) ∈ State S
--   put = there (here refl)
\end{code}

\begin{code}
Maybe : VType → VType
Maybe X = μ ((𝟙 , 𝟘) ∷ (X , 𝟘) ∷ [])

jus : ∀ {Γ V v} → Γ ⊢^v v ∶ V → Γ ⊢^v _ ∶ Maybe V
jus t = con (there (here refl)) t (𝟘-elim (var zero))

nothin : ∀ {Γ V} → Γ ⊢^v _ ∶ Maybe V
nothin = con (here refl) ⟨⟩ (𝟘-elim (var zero))
\end{code}

\begin{code}
abort^Homo : ∀ {Γ Σ X} → Γ ⊢^cs _ ∶ PHomo Abort X 𝟙 Σ (Maybe X)
abort^Homo =  ƛ ƛ ƛ return nothin ∷
              ƛ ƛ return (jus (var (suc zero))) ∷ []
\end{code}

\begin{code}
-- if get then put false else aborting
ex : ∀ {Γ} → Γ ⊢^c _ ∶ (State 𝟚 ++ Abort) ⋆ 𝟙
ex = _to_  (op get · ⟨⟩)
           (if · var zero · thunk (op put · fal) · thunk aborting′) id id
  where
  get : (𝟙 , 𝟚) ∈ (State 𝟚 ++ Abort)
  get = here refl

  put : (𝟚 , 𝟙) ∈ (State 𝟚 ++ Abort)
  put = there (here refl)

  aborting′ : ∀ {Γ V} → Γ ⊢^c _ ∶ (State 𝟚 ++ Abort) ⋆ V
  aborting′ = _to_  (op (there (there (here refl))) · ⟨⟩)
                    (return (𝟘-elim (var zero))) id id
\end{code}

\begin{code}
ex-state′ : ∀ {Γ} → Γ ⊢^c _ ∶ 𝟚 ⇒ Abort ⋆ (𝟙 ⊗ 𝟚)
ex-state′ = run {Σ′ = State 𝟚} state^Homo ex id id

++-comm : ∀ {a}{A : Set a} xs {ys : List A} → xs ++ ys ⊆ ys ++ xs
++-comm xs m = to (++↔++ xs _) ⟨$⟩ m
  where
  open import Data.List.Relation.Unary.Any.Properties
  open import Function.Inverse
  open import Function.Equality
  open Inverse

ex-abort : ∀ {Γ} → Γ ⊢^c _ ∶ 𝟙 ⇒ State 𝟚 ⋆ Maybe 𝟙
ex-abort = run {Σ′ = Abort} abort^Homo ex (++-comm (State 𝟚)) id
\end{code}

\begin{code}
ex-state-abort : ∀ {Γ} → Γ ⊢^c _ ∶ 𝟚 ⇒ [] ⋆ Maybe (𝟙 ⊗ 𝟚)
ex-state-abort = ƛ  (run {Σ′ = Abort} abort^Homo
                    (ex-state′ · var zero) id id · ⟨⟩)

ex-abort-state : ∀ {Γ} → Γ ⊢^c _ ∶ 𝟚 ⇒ [] ⋆ (Maybe 𝟙 ⊗ 𝟚)
ex-abort-state = ƛ  (run {Σ′ = State 𝟚} state^Homo
                    (ex-abort · ⟨⟩) id id · var zero)

test-state-abort : ⟦ ex-state-abort · tru ⟧^c tt ≡
    ⟦ return (jus (⟨⟩ , fal)) ⟧^c tt
test-state-abort = refl

test-abort-state : ⟦ ex-abort-state · tru ⟧^c tt ≡
     ⟦ return (jus ⟨⟩ , fal) ⟧^c tt
test-abort-state = refl -- refl
\end{code}
