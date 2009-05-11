------------------------------------------------------------------------
-- The reflexive transitive closures of McBride, Norell and Jansson
------------------------------------------------------------------------

-- This module could be placed under Relation.Binary. However, since
-- its primary purpose is to be used for _data_ it has been placed
-- under Data instead.

module Data.Star where

open import Relation.Binary
open import Data.Function

infixr 5 _◅_

-- Reflexive transitive closure.

data Star {I : Set} (T : Rel I) : Rel I where
  ε   : Reflexive (Star T)
  _◅_ : ∀ {i j k} (x : T i j) (xs : Star T j k) → Star T i k
        -- The type of _◅_ is Trans T (Star T) (Star T); I expanded
        -- the definition in order to be able to name the arguments (x
        -- and xs).

-- Append/transitivity.

infixr 5 _◅◅_

_◅◅_ : ∀ {I} {T : Rel I} → Transitive (Star T)
ε        ◅◅ ys = ys
(x ◅ xs) ◅◅ ys = x ◅ (xs ◅◅ ys)

-- Sometimes you want to view cons-lists as snoc-lists. Then the
-- following "constructor" is handy. Note that this is _not_ snoc for
-- cons-lists, it is just a synonym for cons (with a different
-- argument order).

infixl 5 _▻_

_▻_ : ∀ {I} {T : Rel I} {i j k} →
      Star T j k → T i j → Star T i k
_▻_ = flip _◅_

-- A corresponding variant of append.

infixr 5 _▻▻_

_▻▻_ : ∀ {I} {T : Rel I} {i j k} →
       Star T j k → Star T i j → Star T i k
_▻▻_ = flip _◅◅_

-- A generalised variant of map which allows the index type to change.

gmap : ∀ {I} {T : Rel I} {J} {U : Rel J} →
       (f : I → J) → T =[ f ]⇒ U → Star T =[ f ]⇒ Star U
gmap f g ε        = ε
gmap f g (x ◅ xs) = g x ◅ gmap f g xs

map : ∀ {I} {T U : Rel I} → T ⇒ U → Star T ⇒ Star U
map = gmap id

-- TransFlip is used to state the type signature of gfold.

TransFlip : ∀ {a} → Rel a → Rel a → Rel a → Set
TransFlip P Q R = ∀ {i j k} → Q j k → P i j → R i k

-- A generalised variant of fold.

gfold : ∀ {I J T} (f : I → J) P →
        Trans     T        (P on₁ f) (P on₁ f) →
        TransFlip (Star T) (P on₁ f) (P on₁ f)
gfold f P _⊕_ ∅ ε        = ∅
gfold f P _⊕_ ∅ (x ◅ xs) = x ⊕ gfold f P _⊕_ ∅ xs

fold : ∀ {I T} (P : Rel I) →
       Trans T P P → Reflexive P → Star T ⇒ P
fold P _⊕_ ∅ = gfold id P _⊕_ ∅

gfoldl : ∀ {I J T} (f : I → J) P →
         Trans (P on₁ f) T        (P on₁ f) →
         Trans (P on₁ f) (Star T) (P on₁ f)
gfoldl f P _⊕_ ∅ ε        = ∅
gfoldl f P _⊕_ ∅ (x ◅ xs) = gfoldl f P _⊕_ (∅ ⊕ x) xs

foldl : ∀ {I T} (P : Rel I) →
        Trans P T P → Reflexive P → Star T ⇒ P
foldl P _⊕_ ∅ = gfoldl id P _⊕_ ∅

concat : ∀ {I} {T : Rel I} → Star (Star T) ⇒ Star T
concat {T = T} = fold (Star T) _◅◅_ ε

-- If the underlying relation is symmetric, then the reflexive
-- transitive closure is also symmetric.

revApp : ∀ {I} {T U : Rel I} → Sym T U →
         ∀ {i j k} → Star T j i → Star U j k → Star U i k
revApp rev ε        ys = ys
revApp rev (x ◅ xs) ys = revApp rev xs (rev x ◅ ys)

reverse : ∀ {I} {T U : Rel I} → Sym T U → Sym (Star T) (Star U)
reverse rev xs = revApp rev xs ε

-- Reflexive transitive closures form a (generalised) monad.

-- return could also be called singleton.

return : ∀ {I} {T : Rel I} → T ⇒ Star T
return x = x ◅ ε

-- A generalised variant of the Kleisli star (flip bind, or
-- concatMap).

kleisliStar : ∀ {I J} {T : Rel I} {U : Rel J} (f : I → J) →
              T =[ f ]⇒ Star U → Star T =[ f ]⇒ Star U
kleisliStar f g = concat ∘ gmap f g

_⋆ : ∀ {I} {T U : Rel I} →
     T ⇒ Star U → Star T ⇒ Star U
_⋆ = kleisliStar id

infixl 1 _>>=_

_>>=_ : ∀ {I} {T U : Rel I} {i j} →
        Star T i j → T ⇒ Star U → Star U i j
m >>= f = (f ⋆) m

-- Note that the monad-like structure above is not an indexed monad
-- (as defined in Category.Monad.Indexed). If it were, then _>>=_
-- would have a type similar to
--
--   ∀ {I} {T U : Rel I} {i j k} →
--   Star T i j → (T i j → Star U j k) → Star U i k.
--                  ^^^^^
-- Note, however, that there is no scope for applying T to any indices
-- in the definition used in Category.Monad.Indexed.
