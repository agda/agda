------------------------------------------------------------------------
-- The Agda standard library
--
-- The partiality monad
------------------------------------------------------------------------

module Category.Monad.Partiality where

open import Coinduction
open import Category.Monad
open import Data.Bool.Base using (Bool; false; true)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product as Prod hiding (map)
open import Data.Sum hiding (map)
open import Function
open import Function.Equivalence using (_⇔_; equivalence)
open import Level using (_⊔_)
open import Relation.Binary as B hiding (Rel)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding (map)
open import Relation.Nullary.Negation

------------------------------------------------------------------------
-- The partiality monad

data _⊥ {a} (A : Set a) : Set a where
  now   : (x : A) → A ⊥
  later : (x : ∞ (A ⊥)) → A ⊥

monad : ∀ {f} → RawMonad {f = f} _⊥
monad = record
  { return = now
  ; _>>=_  = _>>=_
  }
  where
  _>>=_ : ∀ {A B} → A ⊥ → (A → B ⊥) → B ⊥
  now x   >>= f = f x
  later x >>= f = later (♯ (♭ x >>= f))

private module M {f} = RawMonad (monad {f})

-- Non-termination.

never : ∀ {a} {A : Set a} → A ⊥
never = later (♯ never)

-- run x for n steps peels off at most n "later" constructors from x.

run_for_steps : ∀ {a} {A : Set a} → A ⊥ → ℕ → A ⊥
run now   x for n     steps = now x
run later x for zero  steps = later x
run later x for suc n steps = run ♭ x for n steps

-- Is the computation done?

isNow : ∀ {a} {A : Set a} → A ⊥ → Bool
isNow (now x)   = true
isNow (later x) = false

------------------------------------------------------------------------
-- Kinds

-- The partiality monad comes with two forms of equality (weak and
-- strong) and one ordering. Strong equality is stronger than the
-- ordering, which is stronger than weak equality.

-- The three relations are defined using a single data type, indexed
-- by a "kind".

data OtherKind : Set where
  geq weak : OtherKind

data Kind : Set where
  strong : Kind
  other  : (k : OtherKind) → Kind

-- Kind equality is decidable.

infix 4 _≟-Kind_

_≟-Kind_ : Decidable (_≡_ {A = Kind})
_≟-Kind_ strong       strong       = yes P.refl
_≟-Kind_ strong       (other k)    = no λ()
_≟-Kind_ (other k)    strong       = no λ()
_≟-Kind_ (other geq)  (other geq)  = yes P.refl
_≟-Kind_ (other geq)  (other weak) = no λ()
_≟-Kind_ (other weak) (other geq)  = no λ()
_≟-Kind_ (other weak) (other weak) = yes P.refl

-- A predicate which is satisfied only for equalities. Note that, for
-- concrete inputs, this predicate evaluates to ⊤ or ⊥.

Equality : Kind → Set
Equality k = False (k ≟-Kind other geq)

------------------------------------------------------------------------
-- Equality/ordering

module Equality {a ℓ} {A : Set a} -- The "return type".
                (_∼_ : A → A → Set ℓ) where

  -- The three relations.

  data Rel : Kind → A ⊥ → A ⊥ → Set (a ⊔ ℓ) where
    now    : ∀ {k x y} (x∼y : x ∼ y)                         → Rel k         (now   x) (now   y)
    later  : ∀ {k x y} (x∼y : ∞ (Rel k         (♭ x) (♭ y))) → Rel k         (later x) (later y)
    laterʳ : ∀ {x y}   (x≈y :    Rel (other weak) x  (♭ y) ) → Rel (other weak)     x  (later y)
    laterˡ : ∀ {k x y} (x∼y :    Rel (other k) (♭ x)    y  ) → Rel (other k) (later x)        y

  infix 4 _≅_ _≳_ _≲_ _≈_

  _≅_ : A ⊥ → A ⊥ → Set _
  _≅_ = Rel strong

  _≳_ : A ⊥ → A ⊥ → Set _
  _≳_ = Rel (other geq)

  _≲_ : A ⊥ → A ⊥ → Set _
  _≲_ = flip _≳_

  _≈_ : A ⊥ → A ⊥ → Set _
  _≈_ = Rel (other weak)

  -- x ⇓ y means that x terminates with y.

  infix 4 _⇓[_]_ _⇓_

  _⇓[_]_ : A ⊥ → Kind → A → Set _
  x ⇓[ k ] y = Rel k x (now y)

  _⇓_ : A ⊥ → A → Set _
  x ⇓ y = x ⇓[ other weak ] y

  -- x ⇓ means that x terminates.

  infix 4 _⇓

  _⇓ : A ⊥ → Set _
  x ⇓ = ∃ λ v → x ⇓ v

  -- x ⇑ means that x does not terminate.

  infix 4 _⇑[_] _⇑

  _⇑[_] : A ⊥ → Kind → Set _
  x ⇑[ k ] = Rel k x never

  _⇑ : A ⊥ → Set _
  x ⇑ = x ⇑[ other weak ]

------------------------------------------------------------------------
-- Lemmas relating the three relations

module _ {a ℓ} {A : Set a} {_∼_ : A → A → Set ℓ} where

  open Equality _∼_ using (Rel; _≅_; _≳_; _≲_; _≈_; _⇓[_]_; _⇑[_])
  open Equality.Rel

  -- All relations include strong equality.

  ≅⇒ : ∀ {k} {x y : A ⊥} → x ≅ y → Rel k x y
  ≅⇒ (now x∼y)   = now x∼y
  ≅⇒ (later x≅y) = later (♯ ≅⇒ (♭ x≅y))

  -- The weak equality includes the ordering.

  ≳⇒ : ∀ {k} {x y : A ⊥} → x ≳ y → Rel (other k) x y
  ≳⇒ (now x∼y)    = now x∼y
  ≳⇒ (later  x≳y) = later (♯ ≳⇒ (♭ x≳y))
  ≳⇒ (laterˡ x≳y) = laterˡ  (≳⇒    x≳y )

  -- Weak equality includes the other relations.

  ⇒≈ : ∀ {k} {x y : A ⊥} → Rel k x y → x ≈ y
  ⇒≈ {strong}     = ≅⇒
  ⇒≈ {other geq}  = ≳⇒
  ⇒≈ {other weak} = id

  -- The relations agree for non-terminating computations.

  never⇒never : ∀ {k₁ k₂} {x : A ⊥} →
                Rel k₁ x never → Rel k₂ x never
  never⇒never (later  x∼never) = later (♯ never⇒never (♭ x∼never))
  never⇒never (laterʳ x≈never) =          never⇒never    x≈never
  never⇒never (laterˡ x∼never) = later (♯ never⇒never    x∼never)

  -- The "other" relations agree when the right-hand side is a value.

  now⇒now : ∀ {k₁ k₂} {x} {y : A} →
            Rel (other k₁) x (now y) → Rel (other k₂) x (now y)
  now⇒now (now x∼y)      = now x∼y
  now⇒now (laterˡ x∼now) = laterˡ (now⇒now x∼now)

------------------------------------------------------------------------
-- Later can be dropped

  laterʳ⁻¹ : ∀ {k} {x : A ⊥} {y} →
             Rel (other k) x (later y) → Rel (other k) x (♭ y)
  laterʳ⁻¹ (later  x∼y)  = laterˡ        (♭ x∼y)
  laterʳ⁻¹ (laterʳ x≈y)  = x≈y
  laterʳ⁻¹ (laterˡ x∼ly) = laterˡ (laterʳ⁻¹ x∼ly)

  laterˡ⁻¹ : ∀ {x} {y : A ⊥} → later x ≈ y → ♭ x ≈ y
  laterˡ⁻¹ (later  x≈y)  = laterʳ         (♭ x≈y)
  laterˡ⁻¹ (laterʳ lx≈y) = laterʳ (laterˡ⁻¹ lx≈y)
  laterˡ⁻¹ (laterˡ x≈y)  = x≈y

  later⁻¹ : ∀ {k} {x y : ∞ (A ⊥)} →
            Rel k (later x) (later y) → Rel k (♭ x) (♭ y)
  later⁻¹ (later  x∼y)  = ♭ x∼y
  later⁻¹ (laterʳ lx≈y) = laterˡ⁻¹ lx≈y
  later⁻¹ (laterˡ x∼ly) = laterʳ⁻¹ x∼ly

------------------------------------------------------------------------
-- The relations are equivalences or partial orders, given suitable
-- assumptions about the underlying relation

  module Equivalence where

    -- Reflexivity.

    refl : Reflexive _∼_ → ∀ {k} → Reflexive (Rel k)
    refl refl-∼ {x = now v}   = now refl-∼
    refl refl-∼ {x = later x} = later (♯ refl refl-∼)

    -- Symmetry.

    sym : Symmetric _∼_ → ∀ {k} → Equality k → Symmetric (Rel k)
    sym sym-∼ eq (now x∼y)           = now (sym-∼ x∼y)
    sym sym-∼ eq (later         x∼y) = later (♯ sym sym-∼ eq (♭ x∼y))
    sym sym-∼ eq (laterʳ        x≈y) = laterˡ  (sym sym-∼ eq    x≈y )
    sym sym-∼ eq (laterˡ {weak} x≈y) = laterʳ  (sym sym-∼ eq    x≈y )
    sym sym-∼ () (laterˡ {geq}  x≳y)

    -- Transitivity.

    private
     module Trans (trans-∼ : Transitive _∼_) where

      now-trans : ∀ {k x y} {v : A} →
                  Rel k x y → Rel k y (now v) → Rel k x (now v)
      now-trans (now    x∼y) (now    y∼z) = now (trans-∼        x∼y   y∼z)
      now-trans (laterˡ x∼y)         y∼z  = laterˡ (now-trans   x∼y   y∼z)
      now-trans         x∼ly (laterˡ y∼z) = now-trans (laterʳ⁻¹ x∼ly) y∼z

      mutual

        later-trans : ∀ {k} {x y : A ⊥} {z} →
                      Rel k x y → Rel k y (later z) → Rel k x (later z)
        later-trans (later  x∼y)        ly∼lz = later  (♯ trans (♭ x∼y) (later⁻¹  ly∼lz))
        later-trans (laterˡ x∼y)         y∼lz = later  (♯ trans    x∼y  (laterʳ⁻¹  y∼lz))
        later-trans (laterʳ x≈y)        ly≈lz =     later-trans    x≈y  (laterˡ⁻¹ ly≈lz)
        later-trans         x≈y  (laterʳ y≈z) = laterʳ (  trans    x≈y             y≈z )

        trans : ∀ {k} {x y z : A ⊥} → Rel k x y → Rel k y z → Rel k x z
        trans {z = now v}   x∼y y∼v  = now-trans   x∼y y∼v
        trans {z = later z} x∼y y∼lz = later-trans x∼y y∼lz

    open Trans public using (trans)

  -- All the relations are preorders.

  preorder : IsPreorder _≡_ _∼_ → Kind → Preorder _ _ _
  preorder pre k = record
    { Carrier    = A ⊥
    ; _≈_        = _≡_
    ; _∼_        = Rel k
    ; isPreorder = record
      { isEquivalence = P.isEquivalence
      ; reflexive     = refl′
      ; trans         = Equivalence.trans (IsPreorder.trans pre)
      }
    }
    where
    refl′ : ∀ {k} {x y : A ⊥} → x ≡ y → Rel k x y
    refl′ P.refl = Equivalence.refl (IsPreorder.refl pre)

  private
    preorder′ : IsEquivalence _∼_ → Kind → Preorder _ _ _
    preorder′ equiv =
      preorder (Setoid.isPreorder (record { isEquivalence = equiv }))

  -- The two equalities are equivalence relations.

  setoid : IsEquivalence _∼_ →
           (k : Kind) {eq : Equality k} → Setoid _ _
  setoid equiv k {eq} = record
    { Carrier       = A ⊥
    ; _≈_           = Rel k
    ; isEquivalence = record
      { refl  = Pre.refl
      ; sym   = Equivalence.sym (IsEquivalence.sym equiv) eq
      ; trans = Pre.trans
      }
    } where module Pre = Preorder (preorder′ equiv k)

  -- The order is a partial order, with strong equality as the
  -- underlying equality.

  ≳-poset : IsEquivalence _∼_ → Poset _ _ _
  ≳-poset equiv = record
    { Carrier        = A ⊥
    ; _≈_            = _≅_
    ; _≤_            = _≳_
    ; isPartialOrder = record
      { antisym    = antisym
      ; isPreorder = record
        { isEquivalence = S.isEquivalence
        ; reflexive     = ≅⇒
        ; trans         = Pre.trans
        }
      }
    }
    where
    module S   = Setoid (setoid equiv strong)
    module Pre = Preorder (preorder′ equiv (other geq))

    antisym : {x y : A ⊥} → x ≳ y → x ≲ y → x ≅ y
    antisym (now    x∼y)  (now    _)    = now x∼y
    antisym (later  x≳y)  (later  x≲y)  = later (♯ antisym        (♭ x≳y)         (♭ x≲y))
    antisym (later  x≳y)  (laterˡ x≲ly) = later (♯ antisym        (♭ x≳y)  (laterʳ⁻¹ x≲ly))
    antisym (laterˡ x≳ly) (later  x≲y)  = later (♯ antisym (laterʳ⁻¹ x≳ly)        (♭ x≲y))
    antisym (laterˡ x≳ly) (laterˡ x≲ly) = later (♯ antisym (laterʳ⁻¹ x≳ly) (laterʳ⁻¹ x≲ly))

  -- Equational reasoning.

  module Reasoning (isEquivalence : IsEquivalence _∼_) where

    private
      module Pre {k}  = Preorder (preorder′ isEquivalence k)
      module S {k eq} = Setoid (setoid isEquivalence k {eq})

    infix  3 _∎
    infixr 2 _≡⟨_⟩_ _≅⟨_⟩_ _≳⟨_⟩_ _≈⟨_⟩_

    _≡⟨_⟩_ : ∀ {k} x {y z : A ⊥} → x ≡ y → Rel k y z → Rel k x z
    _ ≡⟨ P.refl ⟩ y∼z = y∼z

    _≅⟨_⟩_ : ∀ {k} x {y z : A ⊥} → x ≅ y → Rel k y z → Rel k x z
    _ ≅⟨ x≅y ⟩ y∼z = Pre.trans (≅⇒ x≅y) y∼z

    _≳⟨_⟩_ : ∀ {k} x {y z : A ⊥} →
             x ≳ y → Rel (other k) y z → Rel (other k) x z
    _ ≳⟨ x≳y ⟩ y∼z = Pre.trans (≳⇒ x≳y) y∼z

    _≈⟨_⟩_ : ∀ x {y z : A ⊥} → x ≈ y → y ≈ z → x ≈ z
    _ ≈⟨ x≈y ⟩ y≈z = Pre.trans x≈y y≈z

    sym : ∀ {k} {eq : Equality k} {x y : A ⊥} →
          Rel k x y → Rel k y x
    sym {eq = eq} = S.sym {eq = eq}

    _∎ : ∀ {k} (x : A ⊥) → Rel k x x
    x ∎ = Pre.refl

------------------------------------------------------------------------
-- Lemmas related to now and never

  -- Now is not never.

  now≉never : ∀ {k} {x : A} → ¬ Rel k (now x) never
  now≉never (laterʳ hyp) = now≉never hyp

  -- A partial value is either now or never (classically, when the
  -- underlying relation is reflexive).

  now-or-never : Reflexive _∼_ →
                 ∀ {k} (x : A ⊥) →
                 ¬ ¬ ((∃ λ y → x ⇓[ other k ] y) ⊎ x ⇑[ other k ])
  now-or-never refl x = helper <$> excluded-middle
    where
    open RawMonad ¬¬-Monad

    not-now-is-never : (x : A ⊥) → (∄ λ y → x ≳ now y) → x ≳ never
    not-now-is-never (now x)   hyp with hyp (, now refl)
    ... | ()
    not-now-is-never (later x) hyp =
      later (♯ not-now-is-never (♭ x) (hyp ∘ Prod.map id laterˡ))

    helper : Dec (∃ λ y → x ≳ now y) → _
    helper (yes ≳now) = inj₁ $ Prod.map id ≳⇒ ≳now
    helper (no  ≵now) = inj₂ $ ≳⇒ $ not-now-is-never x ≵now

------------------------------------------------------------------------
-- Map-like results

  -- Map.

  map : ∀ {_∼′_ : A → A → Set a} {k} →
        _∼′_ ⇒ _∼_ → Equality.Rel _∼′_ k ⇒ Equality.Rel _∼_ k
  map ∼′⇒∼ (now x∼y)    = now (∼′⇒∼ x∼y)
  map ∼′⇒∼ (later  x∼y) = later (♯ map ∼′⇒∼ (♭ x∼y))
  map ∼′⇒∼ (laterʳ x≈y) = laterʳ  (map ∼′⇒∼    x≈y)
  map ∼′⇒∼ (laterˡ x∼y) = laterˡ  (map ∼′⇒∼    x∼y)

  -- If a statement can be proved using propositional equality as the
  -- underlying relation, then it can also be proved for any other
  -- reflexive underlying relation.

  ≡⇒ : Reflexive _∼_ →
       ∀ {k x y} → Equality.Rel _≡_ k x y → Rel k x y
  ≡⇒ refl-∼ = map (flip (P.subst (_∼_ _)) refl-∼)

------------------------------------------------------------------------
-- Steps

  -- The number of later constructors (steps) in the terminating
  -- computation x.

  steps : ∀ {k} {x : A ⊥} {y} → x ⇓[ k ] y → ℕ
  steps                (now _)             = zero
  steps .{x = later x} (laterˡ {x = x} x⇓) = suc (steps {x = ♭ x} x⇓)

  module Steps {trans-∼ : Transitive _∼_} where

    left-identity :
      ∀ {k x y} {z : A}
      (x≅y : x ≅ y) (y⇓z : y ⇓[ k ] z) →
      steps (Equivalence.trans trans-∼ (≅⇒ x≅y) y⇓z) ≡ steps y⇓z
    left-identity (now _)     (now _)      = P.refl
    left-identity (later x≅y) (laterˡ y⇓z) =
      P.cong suc $ left-identity (♭ x≅y) y⇓z

    right-identity :
      ∀ {k x} {y z : A}
      (x⇓y : x ⇓[ k ] y) (y≈z : now y ⇓[ k ] z) →
      steps (Equivalence.trans trans-∼ x⇓y y≈z) ≡ steps x⇓y
    right-identity (now x∼y)    (now y∼z) = P.refl
    right-identity (laterˡ x∼y) (now y∼z) =
      P.cong suc $ right-identity x∼y (now y∼z)

------------------------------------------------------------------------
-- Laws related to bind

  -- Never is a left and right "zero" of bind.

  left-zero : {B : Set a} (f : B → A ⊥) → let open M in
              (never >>= f) ≅ never
  left-zero f = later (♯ left-zero f)

  right-zero : ∀ {B} (x : B ⊥) → let open M in
               (x >>= λ _ → never) ≅ never
  right-zero (later x) = later (♯ right-zero (♭ x))
  right-zero (now   x) = never≅never
    where never≅never : never ≅ never
          never≅never = later (♯ never≅never)

  -- Now is a left and right identity of bind (for a reflexive
  -- underlying relation).

  left-identity : Reflexive _∼_ →
                  ∀ {B} (x : B) (f : B → A ⊥) → let open M in
                  (now x >>= f) ≅ f x
  left-identity refl-∼ x f = Equivalence.refl refl-∼

  right-identity : Reflexive _∼_ →
                   (x : A ⊥) → let open M in
                   (x >>= now) ≅ x
  right-identity refl (now   x) = now refl
  right-identity refl (later x) = later (♯ right-identity refl (♭ x))

  -- Bind is associative (for a reflexive underlying relation).

  associative : Reflexive _∼_ →
                ∀ {B C} (x : C ⊥) (f : C → B ⊥) (g : B → A ⊥) →
                let open M in
                (x >>= f >>= g) ≅ (x >>= λ y → f y >>= g)
  associative refl-∼ (now x)   f g = Equivalence.refl refl-∼
  associative refl-∼ (later x) f g =
    later (♯ associative refl-∼ (♭ x) f g)

module _ {s ℓ} {A B : Set s}
         {_∼A_ : A → A → Set ℓ}
         {_∼B_ : B → B → Set ℓ} where

  open Equality
  private
    open module EqA = Equality _∼A_ using () renaming (_⇓[_]_ to _⇓[_]A_; _⇑[_] to _⇑[_]A)
    open module EqB = Equality _∼B_ using () renaming (_⇓[_]_ to _⇓[_]B_; _⇑[_] to _⇑[_]B)

  -- Bind preserves all the relations.

  _>>=-cong_ :
    ∀ {k} {x₁ x₂ : A ⊥} {f₁ f₂ : A → B ⊥} → let open M in
    Rel _∼A_ k x₁ x₂ →
    (∀ {x₁ x₂} → x₁ ∼A x₂ → Rel _∼B_ k (f₁ x₁) (f₂ x₂)) →
    Rel _∼B_ k (x₁ >>= f₁) (x₂ >>= f₂)
  now    x₁∼x₂ >>=-cong f₁∼f₂ = f₁∼f₂ x₁∼x₂
  later  x₁∼x₂ >>=-cong f₁∼f₂ = later (♯ (♭ x₁∼x₂ >>=-cong f₁∼f₂))
  laterʳ x₁≈x₂ >>=-cong f₁≈f₂ = laterʳ (x₁≈x₂ >>=-cong f₁≈f₂)
  laterˡ x₁∼x₂ >>=-cong f₁∼f₂ = laterˡ (x₁∼x₂ >>=-cong f₁∼f₂)

  -- Inversion lemmas for bind.

  >>=-inversion-⇓ :
    Reflexive _∼A_ →
    ∀ {k} x {f : A → B ⊥} {y} → let open M in
    (x>>=f⇓ : (x >>= f) ⇓[ k ]B y) →
    ∃ λ z → ∃₂ λ (x⇓ : x ⇓[ k ]A z) (fz⇓ : f z ⇓[ k ]B y) →
                 steps x⇓ + steps fz⇓ ≡ steps x>>=f⇓
  >>=-inversion-⇓ refl (now x) fx⇓ =
    (x , now refl , fx⇓ , P.refl)
  >>=-inversion-⇓ refl (later x) (laterˡ x>>=f⇓) =
    Prod.map id (Prod.map laterˡ (Prod.map id (P.cong suc))) $
      >>=-inversion-⇓ refl (♭ x) x>>=f⇓

  >>=-inversion-⇑ : IsEquivalence _∼A_ →
                    ∀ {k} x {f : A → B ⊥} → let open M in
                    Rel _∼B_ (other k) (x >>= f) never →
                    ¬ ¬ (x ⇑[ other k ]A ⊎
                         ∃ λ y → x ⇓[ other k ]A y × f y ⇑[ other k ]B)
  >>=-inversion-⇑ eqA {k} x {f} ∼never =
    helper <$> now-or-never IsEqA.refl x
    where
    open RawMonad ¬¬-Monad using (_<$>_)
    open M using (_>>=_)
    open Reasoning eqA
    module IsEqA = IsEquivalence eqA

    k≳ = other geq

    is-never : ∀ {x y} →
               x ⇓[ k≳ ]A y → (x >>= f) ⇑[ k≳ ]B →
               ∃ λ z → (y ∼A z) × f z ⇑[ k≳ ]B
    is-never (now    x∼y)  = λ fx⇑ → (_ , IsEqA.sym x∼y , fx⇑)
    is-never (laterˡ ≳now) = is-never ≳now ∘ later⁻¹

    helper : (∃ λ y → x ⇓[ k≳ ]A y) ⊎ x ⇑[ k≳ ]A →
             x ⇑[ other k ]A ⊎
             ∃ λ y → x ⇓[ other k ]A y × f y ⇑[ other k ]B
    helper (inj₂ ≳never)     = inj₁ (≳⇒ ≳never)
    helper (inj₁ (y , ≳now)) with is-never ≳now (never⇒never ∼never)
    ... | (z , y∼z , fz⇑) = inj₂ (z , ≳⇒ (x     ≳⟨ ≳now ⟩
                                          now y ≅⟨ now y∼z ⟩
                                          now z ∎)
                                    , ≳⇒ fz⇑)

module _ {ℓ} {A B : Set ℓ} {_∼_ : B → B → Set ℓ} where

  open Equality

  -- A variant of _>>=-cong_.

  _≡->>=-cong_ :
    ∀ {k} {x₁ x₂ : A ⊥} {f₁ f₂ : A → B ⊥} → let open M in
    Rel _≡_ k x₁ x₂ →
    (∀ x → Rel _∼_ k (f₁ x) (f₂ x)) →
    Rel _∼_ k (x₁ >>= f₁) (x₂ >>= f₂)
  _≡->>=-cong_ {k} {f₁ = f₁} {f₂} x₁≈x₂ f₁≈f₂ =
    x₁≈x₂ >>=-cong λ {x} x≡x′ →
    P.subst (λ y → Rel _∼_ k (f₁ x) (f₂ y)) x≡x′ (f₁≈f₂ x)

------------------------------------------------------------------------
-- Productivity checker workaround

-- The monad can be awkward to use, due to the limitations of guarded
-- coinduction. The following code provides a (limited) workaround.

module Workaround {a} where

  infixl 1 _>>=_

  data _⊥P : Set a → Set (Level.suc a) where
    now   : ∀ {A} (x : A) → A ⊥P
    later : ∀ {A} (x : ∞ (A ⊥P)) → A ⊥P
    _>>=_ : ∀ {A B} (x : A ⊥P) (f : A → B ⊥P) → B ⊥P

  private

    data _⊥W : Set a → Set (Level.suc a) where
      now   : ∀ {A} (x : A) → A ⊥W
      later : ∀ {A} (x : A ⊥P) → A ⊥W

    mutual

      _>>=W_ : ∀ {A B} → A ⊥W → (A → B ⊥P) → B ⊥W
      now   x >>=W f = whnf (f x)
      later x >>=W f = later (x >>= f)

      whnf : ∀ {A} → A ⊥P → A ⊥W
      whnf (now   x) = now x
      whnf (later x) = later (♭ x)
      whnf (x >>= f) = whnf x >>=W f

  mutual

    private

      ⟦_⟧W : ∀ {A} → A ⊥W → A ⊥
      ⟦ now   x ⟧W = now x
      ⟦ later x ⟧W = later (♯ ⟦ x ⟧P)

    ⟦_⟧P : ∀ {A} → A ⊥P → A ⊥
    ⟦ x ⟧P = ⟦ whnf x ⟧W

  -- The definitions above make sense. ⟦_⟧P is homomorphic with
  -- respect to now, later and _>>=_.

  module Correct where

    private
      open module Eq {A : Set a} = Equality  {A = A} _≡_
      open module R  {A : Set a} = Reasoning (P.isEquivalence {A = A})

    now-hom : ∀ {A} (x : A) → ⟦ now x ⟧P ≅ now x
    now-hom x = now x ∎

    later-hom : ∀ {A} (x : ∞ (A ⊥P)) →
                ⟦ later x ⟧P ≅ later (♯ ⟦ ♭ x ⟧P)
    later-hom x = later (♯ (⟦ ♭ x ⟧P ∎))

    mutual

      private

        >>=-homW : ∀ {A B} (x : B ⊥W) (f : B → A ⊥P) →
                   ⟦ x >>=W f ⟧W ≅ M._>>=_ ⟦ x ⟧W (λ y → ⟦ f y ⟧P)
        >>=-homW (now   x) f = ⟦ f x ⟧P ∎
        >>=-homW (later x) f = later (♯ >>=-hom x f)

      >>=-hom : ∀ {A B} (x : B ⊥P) (f : B → A ⊥P) →
                ⟦ x >>= f ⟧P ≅ M._>>=_ ⟦ x ⟧P (λ y → ⟦ f y ⟧P)
      >>=-hom x f = >>=-homW (whnf x) f

------------------------------------------------------------------------
-- An alternative, but equivalent, formulation of equality/ordering

module AlternativeEquality {a ℓ} where

  private

    El : Setoid a ℓ → Set _
    El = Setoid.Carrier

    Eq : ∀ S → B.Rel (El S) _
    Eq = Setoid._≈_

  open Equality using (Rel)
  open Equality.Rel

  infix  4 _∣_≅P_ _∣_≳P_ _∣_≈P_
  infix  3 _∎
  infixr 2 _≡⟨_⟩_ _≅⟨_⟩_ _≳⟨_⟩_ _≳⟨_⟩≅_ _≳⟨_⟩≈_ _≈⟨_⟩≅_ _≈⟨_⟩≲_
  infixl 1 _>>=_

  mutual

    -- Proof "programs".

    _∣_≅P_ : ∀ S → B.Rel (El S ⊥) _
    _∣_≅P_ = flip RelP strong

    _∣_≳P_ : ∀ S → B.Rel (El S ⊥) _
    _∣_≳P_ = flip RelP (other geq)

    _∣_≈P_ : ∀ S → B.Rel (El S ⊥) _
    _∣_≈P_ = flip RelP (other weak)

    data RelP S : Kind → B.Rel (El S ⊥) (Level.suc (a ⊔ ℓ)) where

      -- Congruences.

      now   : ∀ {k x y} (xRy : x ⟨ Eq S ⟩ y) → RelP S k (now x) (now y)
      later : ∀ {k x y} (x∼y : ∞ (RelP S k (♭ x) (♭ y))) →
              RelP S k (later x) (later y)
      _>>=_ : ∀ {S′ : Setoid a ℓ} {k} {x₁ x₂}
                {f₁ f₂ : El S′ → El S ⊥} →
              let open M in
              (x₁∼x₂ : RelP S′ k x₁ x₂)
              (f₁∼f₂ : ∀ {x y} → x ⟨ Eq S′ ⟩ y →
                       RelP S k (f₁ x) (f₂ y)) →
              RelP S k (x₁ >>= f₁) (x₂ >>= f₂)

      -- Ordering/weak equality.

      laterʳ : ∀   {x y} (x≈y : RelP S (other weak) x (♭ y)) → RelP S (other weak)     x (later y)
      laterˡ : ∀ {k x y} (x∼y : RelP S (other k) (♭ x)   y)  → RelP S (other k) (later x)       y

      -- Equational reasoning. Note that including full transitivity
      -- for weak equality would make _∣_≈P_ trivial; a similar
      -- problem applies to _∣_≳P_ (A ∣ never ≳P now x would be
      -- provable). Instead the definition of RelP includes limited
      -- notions of transitivity, similar to weak bisimulation up-to
      -- various things.

      _∎      : ∀ {k} x → RelP S k x x
      sym     : ∀ {k x y} {eq : Equality k} (x∼y : RelP S k x y) → RelP S k y x
      _≡⟨_⟩_  : ∀ {k} x {y z} (x≡y : x ≡ y) (y∼z : RelP S k y z) → RelP S k x z
      _≅⟨_⟩_  : ∀ {k} x {y z} (x≅y : S ∣ x ≅P y) (y∼z : RelP S k y z) → RelP S k x z
      _≳⟨_⟩_  : let open Equality (Eq S) in
                ∀     x {y z} (x≳y :     x ≳  y) (y≳z : S ∣ y ≳P z) → S ∣ x ≳P z
      _≳⟨_⟩≅_ : ∀     x {y z} (x≳y : S ∣ x ≳P y) (y≅z : S ∣ y ≅P z) → S ∣ x ≳P z
      _≳⟨_⟩≈_ : ∀     x {y z} (x≳y : S ∣ x ≳P y) (y≈z : S ∣ y ≈P z) → S ∣ x ≈P z
      _≈⟨_⟩≅_ : ∀     x {y z} (x≈y : S ∣ x ≈P y) (y≅z : S ∣ y ≅P z) → S ∣ x ≈P z
      _≈⟨_⟩≲_ : ∀     x {y z} (x≈y : S ∣ x ≈P y) (y≲z : S ∣ z ≳P y) → S ∣ x ≈P z

      -- If any of the following transitivity-like rules were added to
      -- RelP, then RelP and Rel would no longer be equivalent:
      --
      --   x ≳P y → y ≳P z → x ≳P z
      --   x ≳P y → y ≳  z → x ≳P z
      --   x ≲P y → y ≈P z → x ≈P z
      --   x ≈P y → y ≳P z → x ≈P z
      --   x ≲  y → y ≈P z → x ≈P z
      --   x ≈P y → y ≳  z → x ≈P z
      --   x ≈P y → y ≈P z → x ≈P z
      --   x ≈P y → y ≈  z → x ≈P z
      --   x ≈  y → y ≈P z → x ≈P z
      --
      -- The reason is that any of these rules would make it possible
      -- to derive that never and now x are related.

  -- RelP is complete with respect to Rel.

  complete : ∀ {S k} {x y : El S ⊥} →
             Equality.Rel (Eq S) k x y → RelP S k x y
  complete (now xRy)    = now xRy
  complete (later  x∼y) = later (♯ complete (♭ x∼y))
  complete (laterʳ x≈y) = laterʳ  (complete    x≈y)
  complete (laterˡ x∼y) = laterˡ  (complete    x∼y)

  -- RelP is sound with respect to Rel.

  private

    -- Proof WHNFs.

    data RelW S : Kind → B.Rel (El S ⊥) (Level.suc (a ⊔ ℓ)) where
      now    : ∀ {k x y} (xRy : x ⟨ Eq S ⟩ y)                 → RelW S k         (now   x) (now   y)
      later  : ∀ {k x y} (x∼y : RelP S k         (♭ x) (♭ y)) → RelW S k         (later x) (later y)
      laterʳ : ∀   {x y} (x≈y : RelW S (other weak) x  (♭ y)) → RelW S (other weak)     x  (later y)
      laterˡ : ∀ {k x y} (x∼y : RelW S (other k) (♭ x)    y)  → RelW S (other k) (later x)        y

    -- WHNFs can be turned into programs.

    program : ∀ {S k x y} → RelW S k x y → RelP S k x y
    program (now    xRy) = now xRy
    program (later  x∼y) = later (♯ x∼y)
    program (laterˡ x∼y) = laterˡ (program x∼y)
    program (laterʳ x≈y) = laterʳ (program x≈y)

    -- Lemmas for WHNFs.

    _>>=W_ : ∀ {A B k x₁ x₂} {f₁ f₂ : El A → El B ⊥} →
             RelW A k x₁ x₂ →
             (∀ {x y} → x ⟨ Eq A ⟩ y → RelW B k (f₁ x) (f₂ y)) →
             RelW B k (M._>>=_ x₁ f₁) (M._>>=_ x₂ f₂)
    now    xRy >>=W f₁∼f₂ = f₁∼f₂ xRy
    later  x∼y >>=W f₁∼f₂ = later  (x∼y >>= program ∘ f₁∼f₂)
    laterʳ x≈y >>=W f₁≈f₂ = laterʳ (x≈y >>=W f₁≈f₂)
    laterˡ x∼y >>=W f₁∼f₂ = laterˡ (x∼y >>=W f₁∼f₂)

    reflW : ∀ {S k} x → RelW S k x x
    reflW {S} (now   x) = now (Setoid.refl S)
    reflW     (later x) = later (♭ x ∎)

    symW : ∀ {S k x y} → Equality k → RelW S k x y → RelW S k y x
    symW {S} eq (now           xRy) = now (Setoid.sym S xRy)
    symW     eq (later         x≈y) = later  (sym {eq = eq} x≈y)
    symW     eq (laterʳ        x≈y) = laterˡ (symW      eq  x≈y)
    symW     eq (laterˡ {weak} x≈y) = laterʳ (symW      eq  x≈y)
    symW     () (laterˡ {geq}  x≈y)

    trans≅W : ∀ {S x y z} →
              RelW S strong x y → RelW S strong y z → RelW S strong x z
    trans≅W {S} (now   xRy) (now   yRz) = now (Setoid.trans S xRy yRz)
    trans≅W     (later x≅y) (later y≅z) = later (_ ≅⟨ x≅y ⟩ y≅z)

    trans≳-W : ∀ {S x y z} → let open Equality (Eq S) in
               x ≳ y → RelW S (other geq) y z → RelW S (other geq) x z
    trans≳-W {S} (now    xRy) (now    yRz) = now (Setoid.trans S xRy yRz)
    trans≳-W     (later  x≳y) (later  y≳z) = later (_ ≳⟨ ♭ x≳y ⟩ y≳z)
    trans≳-W     (later  x≳y) (laterˡ y≳z) = laterˡ (trans≳-W (♭ x≳y) y≳z)
    trans≳-W     (laterˡ x≳y)         y≳z  = laterˡ (trans≳-W    x≳y  y≳z)

    -- Strong equality programs can be turned into WHNFs.

    whnf≅ : ∀ {S x y} → S ∣ x ≅P y → RelW S strong x y
    whnf≅ (now xRy)           = now xRy
    whnf≅ (later x≅y)         = later (♭ x≅y)
    whnf≅ (x₁≅x₂ >>= f₁≅f₂)   = whnf≅ x₁≅x₂ >>=W λ xRy → whnf≅ (f₁≅f₂ xRy)
    whnf≅ (x ∎)               = reflW x
    whnf≅ (sym x≅y)           = symW _ (whnf≅ x≅y)
    whnf≅ (x ≡⟨ P.refl ⟩ y≅z) = whnf≅ y≅z
    whnf≅ (x ≅⟨ x≅y    ⟩ y≅z) = trans≅W (whnf≅ x≅y) (whnf≅ y≅z)

    -- More transitivity lemmas.

    _⟨_⟩≅_ : ∀ {S k} x {y z} →
             RelP S k x y → S ∣ y ≅P z → RelP S k x z
    _⟨_⟩≅_ {k = strong}     x x≅y y≅z = x ≅⟨ x≅y ⟩  y≅z
    _⟨_⟩≅_ {k = other geq}  x x≳y y≅z = x ≳⟨ x≳y ⟩≅ y≅z
    _⟨_⟩≅_ {k = other weak} x x≈y y≅z = x ≈⟨ x≈y ⟩≅ y≅z

    trans∼≅W : ∀ {S k x y z} →
               RelW S k x y → RelW S strong y z → RelW S k x z
    trans∼≅W {S} (now    xRy) (now   yRz) = now (Setoid.trans S xRy yRz)
    trans∼≅W     (later  x∼y) (later y≅z) = later (_ ⟨ x∼y ⟩≅ y≅z)
    trans∼≅W     (laterʳ x≈y) (later y≅z) = laterʳ (trans∼≅W x≈y (whnf≅ y≅z))
    trans∼≅W     (laterˡ x∼y)        y≅z  = laterˡ (trans∼≅W x∼y        y≅z)

    trans≅∼W : ∀ {S k x y z} →
               RelW S strong x y → RelW S k y z → RelW S k x z
    trans≅∼W {S} (now   xRy) (now     yRz) = now (Setoid.trans S xRy yRz)
    trans≅∼W     (later x≅y) (later   y∼z) = later (_ ≅⟨ x≅y ⟩ y∼z)
    trans≅∼W     (later x≅y) (laterˡ  y∼z) = laterˡ (trans≅∼W (whnf≅ x≅y) y∼z)
    trans≅∼W            x≅y  (laterʳ ly≈z) = laterʳ (trans≅∼W        x≅y ly≈z)

    -- Order programs can be turned into WHNFs.

    whnf≳ : ∀ {S x y} → S ∣ x ≳P y → RelW S (other geq) x y
    whnf≳ (now xRy)            = now xRy
    whnf≳ (later  x∼y)         = later (♭ x∼y)
    whnf≳ (laterˡ x≲y)         = laterˡ (whnf≳ x≲y)
    whnf≳ (x₁∼x₂ >>= f₁∼f₂)    = whnf≳ x₁∼x₂ >>=W λ xRy → whnf≳ (f₁∼f₂ xRy)
    whnf≳ (x ∎)                = reflW x
    whnf≳ (sym {eq = ()} x≅y)
    whnf≳ (x ≡⟨ P.refl ⟩  y≳z) = whnf≳ y≳z
    whnf≳ (x ≅⟨ x≅y    ⟩  y≳z) = trans≅∼W (whnf≅ x≅y) (whnf≳ y≳z)
    whnf≳ (x ≳⟨ x≳y    ⟩  y≳z) = trans≳-W        x≳y  (whnf≳ y≳z)
    whnf≳ (x ≳⟨ x≳y    ⟩≅ y≅z) = trans∼≅W (whnf≳ x≳y) (whnf≅ y≅z)

    -- Another transitivity lemma.

    trans≳≈W : ∀ {S x y z} →
               RelW S (other geq) x y → RelW S (other weak) y z →
               RelW S (other weak) x z
    trans≳≈W {S} (now    xRy) (now    yRz) = now (Setoid.trans S xRy yRz)
    trans≳≈W     (later  x≳y) (later  y≈z) = later (_ ≳⟨ x≳y ⟩≈ y≈z)
    trans≳≈W     (laterˡ x≳y)         y≈z  = laterˡ (trans≳≈W        x≳y  y≈z)
    trans≳≈W             x≳y  (laterʳ y≈z) = laterʳ (trans≳≈W        x≳y  y≈z)
    trans≳≈W     (later  x≳y) (laterˡ y≈z) = laterˡ (trans≳≈W (whnf≳ x≳y) y≈z)

    -- All programs can be turned into WHNFs.

    whnf : ∀ {S k x y} → RelP S k x y → RelW S k x y
    whnf (now xRy)            = now xRy
    whnf (later  x∼y)         = later     (♭ x∼y)
    whnf (laterʳ x≈y)         = laterʳ (whnf x≈y)
    whnf (laterˡ x∼y)         = laterˡ (whnf x∼y)
    whnf (x₁∼x₂ >>= f₁∼f₂)    = whnf x₁∼x₂ >>=W λ xRy → whnf (f₁∼f₂ xRy)
    whnf (x ∎)                = reflW x
    whnf (sym {eq = eq} x≈y)  = symW eq (whnf x≈y)
    whnf (x ≡⟨ P.refl ⟩  y∼z) = whnf y∼z
    whnf (x ≅⟨ x≅y    ⟩  y∼z) = trans≅∼W (whnf x≅y) (whnf y∼z)
    whnf (x ≳⟨ x≳y    ⟩  y≳z) = trans≳-W       x≳y  (whnf y≳z)
    whnf (x ≳⟨ x≳y    ⟩≅ y≅z) = trans∼≅W (whnf x≳y) (whnf y≅z)
    whnf (x ≳⟨ x≳y    ⟩≈ y≈z) = trans≳≈W (whnf x≳y) (whnf y≈z)
    whnf (x ≈⟨ x≈y    ⟩≅ y≅z) = trans∼≅W (whnf x≈y) (whnf y≅z)
    whnf (x ≈⟨ x≈y    ⟩≲ y≲z) = symW _ (trans≳≈W (whnf y≲z) (symW _ (whnf x≈y)))

  mutual

    -- Soundness.

    private

      soundW : ∀ {S k x y} → RelW S k x y → Rel (Eq S) k x y
      soundW (now    xRy) = now xRy
      soundW (later  x∼y) = later (♯ sound  x∼y)
      soundW (laterʳ x≈y) = laterʳ  (soundW x≈y)
      soundW (laterˡ x∼y) = laterˡ  (soundW x∼y)

    sound : ∀ {S k x y} → RelP S k x y → Rel (Eq S) k x y
    sound x∼y = soundW (whnf x∼y)

  -- RelP and Rel are equivalent (when the underlying relation is an
  -- equivalence).

  correct : ∀ {S k x y} → RelP S k x y ⇔ Rel (Eq S) k x y
  correct = equivalence sound complete

------------------------------------------------------------------------
-- Another lemma

-- Bind is "idempotent".

idempotent :
  ∀ {ℓ} {A : Set ℓ} (B : Setoid ℓ ℓ) →
  let open M; open Setoid B using (_≈_; Carrier); open Equality _≈_ in
  (x : A ⊥) (f : A → A → Carrier ⊥) →
  (x >>= λ y′ → x >>= λ y″ → f y′ y″) ≳ (x >>= λ y′ → f y′ y′)
idempotent {A = A} B x f = sound (idem x)
  where
  open AlternativeEquality hiding (_>>=_)
  open M
  open Equality.Rel using (laterˡ)
  open Equivalence using (refl)

  idem : (x : A ⊥) →
         B ∣ (x >>= λ y′ → x >>= λ y″ → f y′ y″) ≳P
             (x >>= λ y′ → f y′ y′)
  idem (now   x) = f x x ∎
  idem (later x) = later (♯ (
    (♭ x >>= λ y′ → later x >>= λ y″ → f y′ y″)  ≳⟨ (refl P.refl {x = ♭ x} ≡->>=-cong λ _ →
                                                     laterˡ (refl (Setoid.refl B))) ⟩
    (♭ x >>= λ y′ →     ♭ x >>= λ y″ → f y′ y″)  ≳⟨ idem (♭ x) ⟩≅
    (♭ x >>= λ y′ → f y′ y′)                     ∎))

------------------------------------------------------------------------
-- Example

private
 module Example where

  open Data.Nat
  open Workaround

  -- McCarthy's f91:

  f91′ : ℕ → ℕ ⊥P
  f91′ n with n ≤? 100
  ... | yes _ = later (♯ (f91′ (11 + n) >>= f91′))
  ... | no  _ = now (n ∸ 10)

  f91 : ℕ → ℕ ⊥
  f91 n = ⟦ f91′ n ⟧P
