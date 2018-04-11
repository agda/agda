
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

F : Bool → Set
F false = Bool
F true  = Nat

f : ∀ b → F b → Nat
f false false = 0
f false true  = 1
f true  x     = 2

data D : Nat → Set where
  mkD : (b : Bool) (x : F b) → D (f b x)

mutual
  ?X : Nat → Set
  ?X = _

  ?b : Nat → Bool
  ?b = _

  -- Here we should check
  --    (n : Nat) → ?X n == (x : F (?b 0)) → D (f (?b 0) x)
  -- and get stuck on comparing the domains, but special inference
  -- for constructors is overeager and compares the target types,
  -- solving
  --    ?X : Nat → Set
  --    ?X x := D (f (?b 0) x)
  -- Note that the call to f is not well-typed unless we solve the
  -- (as yet unsolved) constraint Nat == F (?b 0).
  constr₁ : (n : Nat) → ?X n
  constr₁ = mkD (?b 0)

  -- Now we can form other constraints on ?X. This one simplifies to
  --   f (?b 0) 1 ≡ 0      (*)
  constr₂ : ?X 1 ≡ D 0
  constr₂ = refl

  -- Finally, we pick the wrong solution for ?b, causing (*) to become
  --   f false 1 ≡ 0
  -- which crashes with an impossible when we try to reduce the call to f.
  solve-b : ?b ≡ λ _ → false
  solve-b = refl
