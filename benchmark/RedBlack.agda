module RedBlack where

open import Prelude hiding (insert)
open import TheList
open import Fold
open import Extra

-- Version of comparison that lets us use instance search for the proof objects.
data Comparison! {a} {A : Set a} (_<_ : A → A → Set a) (x y : A) : Set a where
  less    : {{_ : x < y}} → Comparison! _<_ x y
  equal   : {{_ : x ≡ y}} → Comparison! _<_ x y
  greater : {{_ : y < x}} → Comparison! _<_ x y

compare! : ∀ {a} {A : Set a} {{_ : Ord A}} (x y : A) → Comparison! _<_ x y
compare! x y =
  case compare x y of λ where
    (less    lt) → less    {{lt}}
    (equal   eq) → equal   {{eq}}
    (greater gt) → greater {{gt}}

record Prf (A : Set) : Set where
  constructor !
  field
    {{prf}} : A

data Bound (A : Set) : Set where
  -∞ ∞ : Bound A
  # : A → Bound A

module _ {A : Set} {{_ : Ord A}} where
  LessBound : Bound A → Bound A → Set
  LessBound ∞ _ = ⊥
  LessBound _ ∞ = ⊤
  LessBound _ -∞ = ⊥
  LessBound -∞ _ = ⊤
  LessBound (# x) (# y) = x < y

  instance
    OrdBound : Ord (Bound A)
    OrdBound = defaultOrd compareBound
      where
        compareBound : (a b : Bound A) → Comparison LessBound a b
        compareBound -∞ -∞ = equal refl
        compareBound -∞ ∞ = less _
        compareBound -∞ (# x) = less _
        compareBound ∞ -∞ = greater tt
        compareBound ∞ ∞ = equal refl
        compareBound ∞ (# x) = greater tt
        compareBound (# x) -∞ = greater tt
        compareBound (# x) ∞ = less tt
        compareBound (# x) (# y) with compare x y
        ... | less lt = less lt
        ... | greater gt = greater gt
        compareBound (# x) (# .x) | equal refl = equal refl

Bounds : Set → Set
Bounds A = Bound A × Bound A

Rel : Set → Set₁
Rel A = Bounds A → Set

module _ {A : Set} where
  PrfR : Rel A → Rel A
  PrfR R b = Prf (R b)

  data _∧_ (S T : Rel A) : Rel A where
    pivot : ∀ {l u} p → S (l , # p) → T (# p , u) → (S ∧ T) (l , u)

  pattern -⟨_⟩- p = pivot p ! !
  pattern _⟨_⟩_ l p r = pivot p l r

module _ {A : Set} {{_ : Ord A}} where
  Less : Rel A
  Less = PrfR (uncurry _<_)

  Bounded : Rel A
  Bounded = Less ∧ Less

data Color : Set where
  red black : Color

module _ (A : Set) {{_ : Ord A}} where

  data Tree′ (b : Bounds A) : Nat → Color → Set

  Tree : Nat → Color → Rel A
  Tree n c b = Tree′ b n c

  data Tree′ b where
    leaf′  : Less b → Tree 0 black b
    red   : ∀ {n} → (Tree n black ∧ Tree n black) b → Tree n red b
    black : ∀ {c₁ c₂ n} → (Tree n c₁ ∧ Tree n c₂) b → Tree (suc n) black b

  pattern leaf = leaf′ !

  data PreTree′ (b : Bounds A) (n : Nat) : Color → Set

  PreTree : Nat → Color → Bounds A → Set
  PreTree n c b = PreTree′ b n c

  data PreTree′ b n where
    red         : ∀ {c₁ c₂} → (Tree n c₁ ∧ Tree n c₂) b → PreTree n red b
    maybe-black : ∀ {c} → Tree n c b → PreTree n black b

  pattern _b⟨_⟩_   l x r = black (l ⟨ x ⟩ r)
  pattern _r⟨_⟩_   l x r = red (l ⟨ x ⟩ r)
  pattern _pb⟨_⟩_  l x r = maybe-black (black (l ⟨ x ⟩ r))
  pattern _pbr⟨_⟩_ l x r = maybe-black (red   (l ⟨ x ⟩ r))
  pattern _rbb⟨_⟩_ l x r = red {c₁ = black} {c₂ = black} (l ⟨ x ⟩ r)

module _ {A : Set} {{_ : Ord A}} where

  balance-l : ∀ {b c₁ c₂ n} →
              (PreTree A n c₁ ∧ Tree A n c₂) b →
              PreTree A (suc n) black b
  balance-l (((l₁ r⟨ z ⟩ l₂) r⟨ x ⟩ l₃) ⟨ y ⟩ r) =
    (l₁ b⟨ z ⟩ l₂) pbr⟨ x ⟩ (l₃ b⟨ y ⟩ r)
  balance-l ((l₁ r⟨ z ⟩ (l₂ r⟨ x ⟩ l₃)) ⟨ y ⟩ r) =
    (l₁ b⟨ z ⟩ l₂) pbr⟨ x ⟩ (l₃ b⟨ y ⟩ r)
  balance-l ((l₁ rbb⟨ x ⟩ l₂) ⟨ y ⟩ r) =
    (l₁ r⟨ x ⟩ l₂) pb⟨ y ⟩ r
  balance-l (maybe-black l ⟨ y ⟩ r) = l pb⟨ y ⟩ r

  balance-r : ∀ {b c₁ c₂ n} →
              (Tree A n c₁ ∧ PreTree A n c₂) b →
              PreTree A (suc n) black b
  balance-r (l ⟨ y ⟩ ((r₁ r⟨ z ⟩ r₂) r⟨ x ⟩ r₃)) =
    (l b⟨ y ⟩ r₁) pbr⟨ z ⟩ (r₂ b⟨ x ⟩ r₃)
  balance-r (l ⟨ y ⟩ (r₁ r⟨ x ⟩ (r₂ r⟨ z ⟩ r₃))) =
    (l b⟨ y ⟩ r₁) pbr⟨ x ⟩ (r₂ b⟨ z ⟩ r₃)
  balance-r (l ⟨ y ⟩ (r₁ rbb⟨ x ⟩ r₂)) =
    l pb⟨ y ⟩ (r₁ r⟨ x ⟩ r₂)
  balance-r (l ⟨ y ⟩ maybe-black r) = l pb⟨ y ⟩ r

  ins : ∀ {b c n} → Bounded b → Tree A n c b → PreTree A n c b
  ins -⟨ x ⟩- leaf = leaf pbr⟨ x ⟩ leaf
  ins -⟨ x ⟩- (red (l ⟨ y ⟩ r)) =
    case compare! x y of λ where
      less    → case ins -⟨ x ⟩- l of λ { (maybe-black l′) → l′ r⟨ y ⟩ r }
      greater → case ins -⟨ x ⟩- r of λ { (maybe-black r′) → l r⟨ y ⟩ r′ }
      equal   → l r⟨ y ⟩ r
  ins -⟨ x ⟩- (black (l ⟨ y ⟩ r)) =
    case compare! x y of λ where
      less    → balance-l (ins -⟨ x ⟩- l ⟨ y ⟩ r)
      greater → balance-r (l ⟨ y ⟩ ins -⟨ x ⟩- r)
      equal   → l pb⟨ y ⟩ r

data RedBlackTree (A : Set) {{_ : Ord A}} : Set where
  mkT : ∀ {n} → Tree A n black (-∞ , ∞) → RedBlackTree A

module _ {A : Set} {{_ : Ord A}} where

  insert : A → RedBlackTree A → RedBlackTree A
  insert x (mkT t) with ins -⟨ x ⟩- t
  ... | l pbr⟨ y ⟩ r      = mkT $ l b⟨ y ⟩ r
  ... | l  pb⟨ y ⟩ r      = mkT $ l b⟨ y ⟩ r
  ... | maybe-black leaf = mkT leaf

  fromList : List A → RedBlackTree A
  -- we changed `foldr` here to `foldl!` for efficiency reasons
  fromList = myfold (flip insert) (mkT leaf)

  toList′ : ∀ {b n c} → Tree′ A b n c → List A → List A
  toList′ (leaf′ _)   xs = xs
  toList′ (l r⟨ x ⟩ r) xs = toList′ l (x ∷ toList′ r xs)
  toList′ (l b⟨ x ⟩ r) xs = toList′ l (x ∷ toList′ r xs)

  toList : RedBlackTree A → List A
  toList (mkT t) = toList′ t []

  treeSort : List A → List A
  treeSort = toList ∘ fromList

-------------
-- Example --
-------------

main : IO Unit
main = putStrLn $ show $ sum $ theList
-- main = putStrLn $ show $ sum $ treeSort theList
