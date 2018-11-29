
open import Agda.Builtin.Equality

_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ x = x

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

record IsRG (Node : Set) (Edge : Set) : Set where
  field
    src : Edge → Node
    tgt : Edge → Node
    rfl : Node → Edge
    eq-src-rfl : ∀{x} → src (rfl x) ≡ x
    eq-tgt-rfl : ∀{x} → tgt (rfl x) ≡ x
open IsRG {{...}} public

module norecord where

  source : ∀{Node Edge : Set} {{i : IsRG Node Edge}} → Edge → Node
  source x = src x

  lemma1 : ∀{Node Edge : Set} {{i : IsRG Node Edge}} → (e : Edge) → (Node ∋ source e) ≡ src e
  lemma1 e = refl

  rfl-src : ∀{Node Edge : Set} {{i : IsRG Node Edge}} → Edge → Edge
  rfl-src {Node} e = rfl (Node ∋ src e)

  lemma2 : ∀{Node Edge : Set} {{i : IsRG Node Edge}} → (n : Node) → rfl-src {Node} (rfl n) ≡ (Edge ∋ rfl n)
  lemma2 {Node}{Edge} n = cong (rfl {Node = Node}) (eq-src-rfl {Edge = Edge})

module yesrecord where

  record RG : Set₁ where
    constructor mkRG
    field
      Node : Set
      Edge : Set
      {{isRG}} : IsRG Node Edge
  open RG public

  source : ∀{rg} → Edge rg → Node rg
  source x = src x

  lemma1 : ∀{rg} → (e : Edge rg) → (Node rg ∋ source {mkRG (Node rg) (Edge rg)} e) ≡ src e
  --causes problems:
  --lemma1 : ∀{rg} → (e : Edge rg) → (Node rg ∋ source {_} e) ≡ src e
  lemma1 e = refl

  rfl-src : ∀{rg} → Edge rg → Edge rg
  rfl-src {rg} e = rfl (Node rg ∋ src e)

  lemma2 : ∀{rg} → (n : Node rg) → rfl-src {rg} (rfl n) ≡ (Edge rg ∋ rfl n)
  lemma2 {rg} n = cong (rfl {Node = Node rg}) (eq-src-rfl {Edge = Edge rg})
