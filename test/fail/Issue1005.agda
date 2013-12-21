
postulate
  X : Set
  T : X → Set
  H : ∀ x → T x → Set

g : ∀ x → T x → Set
g x t = ∀ x → H x t
