open import Agda.Primitive.Cubical

test : (J : IUniv) → J → J
test J j = primHComp {φ = i0} (λ k → λ ()) j
