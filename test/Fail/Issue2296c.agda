
data Id (A : Set) : Set where
  wrap : A → Id A

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

maybe : {A : Set} {B : Maybe A → Set} →
        ((x : A) → B (just x)) → B nothing → (x : Maybe A) → B x
maybe j n (just x) = j x
maybe j n nothing  = n

record MaybeT (M : Set → Set) (A : Set) : Set where
  constructor wrap
  field
    run : M (Maybe A)

open MaybeT public

postulate
  R : Set
  r : R

module M (_ : R) where

  record Monad (M : Set → Set) : Set₁ where
    field
      return : ∀ {A} → A → M A
      _>>=_  : ∀ {A B} → M A → (A → M B) → M B

  open Monad ⦃ … ⦄ public

  instance

    transform : {M : Set → Set} ⦃ is-raw-monad : Monad M ⦄ →
                Monad (MaybeT M)
    run (Monad.return transform x)   = return (just x)
    run (Monad._>>=_  transform x f) =
      run x >>= maybe (λ x → run (f x)) (return nothing)

open M r

instance

  id-raw-monad : Monad Id
  Monad.return id-raw-monad            = wrap
  Monad._>>=_  id-raw-monad (wrap x) f = f x

postulate
  _∼_      : {A : Set} → Id A → Id A → Set
  refl     : {A : Set} (x : Id A) → x ∼ x
  trans    : {A : Set} {x y z : Id A} → x ∼ y → y ∼ z → x ∼ z
  id       : {A : Set} {x : Id A} (y : Id A) → x ∼ y → x ∼ y
  >>=-cong : {A : Set} (x : Id A) {f g : A → Id A} →
             (∀ z → f z ∼ g z) → (x >>= f) ∼ (x >>= g)
  assoc    : {A : Set} (x : Id A) (f : A → Id A) (g : A → Id A) →
             (x >>= (λ x → f x >>= g)) ∼ ((x >>= f) >>= g)

fails :
  {A : Set}
  (x : MaybeT Id A) (f : A → MaybeT Id A) (g : A → MaybeT Id A) →
  run (x >>= λ x → f x >>= g) ∼ run ((x >>= f) >>= g)
fails x f g =
  trans (>>=-cong (run x) (maybe (λ _ → refl _) (refl _)))
        (id (run ((x >>= f) >>= g))
            (assoc (run x) _ _))
