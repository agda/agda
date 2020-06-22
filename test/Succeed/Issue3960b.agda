
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

data Unit : Set where
  unit : Unit

record _∼_ (From To : Set) : Set where
  field
    to      : From → To
    from    : To → From
    to-from : ∀ {x} → to (from x) ≡ x

postulate
  P : {A : Set} → A → Set
  f : {A B : Set} (A∼B : A ∼ B) (x : A) → P (_∼_.to A∼B x) ∼ P x

record R : Set where
  field
    p   : {x y : Unit} → P x → P y
    u v : Unit

g : (r : R) → _ ∼ P r
g = f lemma
  where
  lemma : R ∼ Σ _ λ _ → Σ _ λ (_ : ∀ {x y} → _ → _) → _
  lemma = record
    { to      = λ x → R.u x , R.p x , R.v x
    ; from    = λ { (u , p , v) → record
                    { u  = u
                    ; p  = λ {x y} → p {x = x} {y = y}
                    ; v  = v
                    } }
    ; to-from = refl
    }
