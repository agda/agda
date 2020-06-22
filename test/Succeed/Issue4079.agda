open import Agda.Builtin.Bool
open import Agda.Builtin.List

data Singleton : List Bool → Set where
  singleton : ∀ b → Singleton (b ∷ [])

Works : (bs : List Bool) → Singleton bs → Set₁
Works bs s with s
... | singleton b with Set
Works .(b ∷ []) s | singleton b | _ = Set

Fails : (bs : List Bool) → Singleton bs → Set₁
Fails bs        s with singleton b ← s with Set
Fails .(b ∷ []) s | _ = Set
