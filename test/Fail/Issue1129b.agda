
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

postulate
  M   : Set → Set
  _>>=_ : ∀{A B : Set} → M A → (A → M B) → M B

infixr 1 bind
bind : _
bind = _>>=_

infix 0 id
id : ∀{A : Set} → A → A
id = λ x → x

syntax id  x             = act x
syntax bind ma (λ x → f) = x ← ma , f

swapM′ : ∀ {A B} → M (A × B) → M (B × A)
swapM′ mAB =
  act
     (a , b) ← mAB
   , return $ b , a

-- Was:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error:
-- src/full/Agda/TypeChecking/Monad/Base.hs:1793
