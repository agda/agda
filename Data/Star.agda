------------------------------------------------------------------------
-- The reflexive transitive closures of McBride, Norell and Jansson
------------------------------------------------------------------------

-- This module could be placed under Relation.Binary. However, since
-- its primary purpose is to be used for _data_ it has been placed
-- under Data instead.

module Data.Star where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Function
import Relation.Binary.PreorderReasoning as PreR

infixr 5 _◅_

-- Reflexive transitive closure.

data Star {I : Set} (T : Rel I) : Rel I where
  ε   : Reflexive (Star T)
  _◅_ : Trans T (Star T) (Star T)

-- Append/transitivity.

infixr 5 _◅◅_

_◅◅_ : forall {I} {T : Rel I} -> Transitive (Star T)
ε        ◅◅ ys = ys
(x ◅ xs) ◅◅ ys = x ◅ (xs ◅◅ ys)

◅◅-assoc : forall {I} {T : Rel I} {i j k l}
                  (xs : Star T i j) (ys : Star T j k)
                  (zs : Star T k l) ->
           (xs ◅◅ ys) ◅◅ zs ≡ xs ◅◅ (ys ◅◅ zs)
◅◅-assoc ε        ys zs = ≡-refl
◅◅-assoc (x ◅ xs) ys zs = ≡-cong (_◅_ x) (◅◅-assoc xs ys zs)

-- Sometimes you want to view cons-lists as snoc-lists. Then the
-- following "constructor" is handy. Note that this is _not_ snoc for
-- cons-lists, it is just a synonym for cons (with a different
-- argument order).

infixl 5 _▻_

_▻_ : forall {I} {T : Rel I} {i j k} ->
      Star T j k -> T i j -> Star T i k
_▻_ = flip _◅_

-- A corresponding variant of append.

infixr 5 _▻▻_

_▻▻_ : forall {I} {T : Rel I} {i j k} ->
       Star T j k -> Star T i j -> Star T i k
_▻▻_ = flip _◅◅_

-- A generalised variant of map which allows the index type to change.

gmap : forall {I} {T : Rel I} {J} {U : Rel J} ->
       (f : I -> J) -> T =[ f ]⇒ U -> Star T =[ f ]⇒ Star U
gmap f g ε        = ε
gmap f g (x ◅ xs) = g x ◅ gmap f g xs

map : forall {I} {T U : Rel I} -> T ⇒ U -> Star T ⇒ Star U
map = gmap id

-- A generalised variant of fold.

gfold : forall {I J T} (f : I -> J) P ->
        Trans T (P on₁ f) (P on₁ f) -> Reflexive (P on₁ f) ->
        Star T =[ f ]⇒ P
gfold f P _⊕_ ∅ ε        = ∅
gfold f P _⊕_ ∅ (x ◅ xs) = x ⊕ gfold f P _⊕_ ∅ xs

fold : forall {I T} (P : Rel I) ->
       Trans T P P -> Reflexive P -> Star T ⇒ P
fold = gfold id

gfoldl : forall {I J T} (f : I -> J) P ->
         Trans (P on₁ f) T        (P on₁ f) ->
         Trans (P on₁ f) (Star T) (P on₁ f)
gfoldl f P _⊕_ ∅ ε        = ∅
gfoldl f P _⊕_ ∅ (x ◅ xs) = gfoldl f P _⊕_ (∅ ⊕ x) xs

foldl : forall {I T} (P : Rel I) ->
        Trans P T        P ->
        Trans P (Star T) P
foldl = gfoldl id

concat : forall {I} {T : Rel I} -> Star (Star T) ⇒ Star T
concat {T = T} = fold (Star T) _◅◅_ ε

-- If the underlying relation is symmetric, then the reflexive
-- transitive closure is also symmetric.

revApp : forall {I} {T U : Rel I} -> Sym T U ->
         forall {i j k} -> Star T j i -> Star U j k -> Star U i k
revApp rev ε        ys = ys
revApp rev (x ◅ xs) ys = revApp rev xs (rev x ◅ ys)

reverse : forall {I} {T U : Rel I} -> Sym T U -> Sym (Star T) (Star U)
reverse rev xs = revApp rev xs ε

-- Reflexive transitive closures form a (generalised) monad.

-- return could also be called singleton.

return : forall {I} {T : Rel I} -> T ⇒ Star T
return x = x ◅ ε

-- A generalised variant of the Kleisli star (flip bind, or
-- concatMap).

kleisliStar : forall {I J} {T : Rel I} {U : Rel J} (f : I -> J) ->
              T =[ f ]⇒ Star U -> Star T =[ f ]⇒ Star U
kleisliStar f g = concat ∘ gmap f g

_⋆ : forall {I} {T U : Rel I} ->
     T ⇒ Star U -> Star T ⇒ Star U
_⋆ = kleisliStar id

infixl 1 _>>=_

_>>=_ : forall {I} {T U : Rel I} {i j} ->
        Star T i j -> T ⇒ Star U -> Star U i j
m >>= f = (f ⋆) m

-- Note that the monad-like structure above is not an indexed monad
-- (as defined in Category.Monad.Indexed). If it were, then _>>=_
-- would have a type similar to
--
--   forall {I} {T U : Rel I} {i j k} ->
--   Star T i j -> (T i j -> Star U j k) -> Star U i k.
--                  ^^^^^
-- Note, however, that there is no scope for applying T to any indices
-- in the definition used in Category.Monad.Indexed.

-- Reflexive transitive closures are preorders.

starPreorder : forall {I} (T : Rel I) -> Preorder
starPreorder {I} T = record
  { carrier    = I
  ; _≈_        = _≡_
  ; _∼_        = Star T
  ; isPreorder = record
    { isEquivalence = ≡-isEquivalence
    ; reflexive     = reflexive
    ; trans         = _◅◅_
    ; ≈-resp-∼      = ≡-resp (Star T)
    }
  }
  where
  reflexive : _≡_ ⇒ Star T
  reflexive ≡-refl = ε

-- Preorder reasoning for Star.

module StarReasoning {I : Set} (T : Rel I) where
  open PreR (starPreorder T) public
    renaming (_∼⟨_⟩_ to _⟶⋆⟨_⟩_)

  infixr 2 _⟶⟨_⟩_

  _⟶⟨_⟩_ : forall x {y z} -> T x y -> y IsRelatedTo z -> x IsRelatedTo z
  x ⟶⟨ x⟶y ⟩ y⟶⋆z = x ⟶⋆⟨ x⟶y ◅ ε ⟩ y⟶⋆z
