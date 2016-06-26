-- Andreas, 2016-06-26, issue #2059 reported by IanOrton

-- An irrelevant parameter in a rewrite rule should still
-- be bound by the lhs.

{-# OPTIONS --rewriting #-}

-- {-# OPTIONS -v tc.pos:10 #-}
-- {-# OPTIONS -v tc.polarity:10 #-}

open import Common.Equality
open import Common.Bool

data ⊥ : Set where

⊥-elim : ∀{a}{A : Set a} → .⊥ → A
⊥-elim ()

_∧_ : (a b : Bool) → Bool
true  ∧ b = b
false ∧ _ = false

obvious : (b b' : Bool) .(p : b ≡ b' → ⊥) → (b ∧ b') ≡ false
obvious false b'    notEq = refl
obvious true  false notEq = refl
obvious true  true  notEq = ⊥-elim (notEq refl)

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE obvious   #-}

-- Should give error:

-- obvious  is not a legal rewrite rule,
-- since the following variables are not bound by the left hand side:  p
-- when checking the pragma REWRITE obvious

oops : (b : Bool) → b ∧ b ≡ false
oops b = refl

true≢false : true ≡ false → ⊥
true≢false ()

bot : ⊥
bot = true≢false (oops true)
