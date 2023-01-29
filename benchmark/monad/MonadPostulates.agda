------------------------------------------------------------------------
-- Parser monad
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.OrderMorphism
open import Relation.Binary.PropositionalEquality hiding (poset)
import Relation.Binary.Properties.StrictTotalOrder as STOProps
open import Data.Product
open import Level

module MonadPostulates where

postulate
  -- Input string positions.

  Position : Set
  _<P_ : Rel Position zero
  posOrdered : IsStrictTotalOrder _≡_ _<P_

  -- Input strings.

  Input : Position -> Set

  -- In order to be able to store results in a memo table (and avoid
  -- having to lift the table code to Set1) the result types have to
  -- come from the following universe:

  Result : Set
  ⟦_⟧ : Result -> Set

  -- Memoisation keys. These keys must uniquely identify the
  -- computation that they are associated with, when paired up with
  -- the current input string position.

  Key : let PosPoset = STOProps.poset
                          (record { Carrier = _ ; _≈_ = _; _<_ = _
                                  ; isStrictTotalOrder = posOrdered })
            MonoFun = PosPoset ⇒-Poset PosPoset in
         MonoFun -> Result -> Set
  _≈'_ _<_ : Rel (∃₂ Key) zero
  keyOrdered : IsStrictTotalOrder _≈'_ _<_

  -- Furthermore the underlying equality needs to be strong enough.

  funsEqual    : _≈'_ =[ proj₁ ]⇒ _≡_
  resultsEqual : _≈'_ =[ (\rfk -> proj₁ (proj₂ rfk)) ]⇒ _≡_

--  where

open _⇒-Poset_
open STOProps (record { Carrier = _ ; _≈_ = _; _<_ = _
                      ; isStrictTotalOrder = posOrdered })

import IndexedMap as Map -- renaming (Map to MemoTable)
open import Category.Monad
open import Category.Monad.State
import Data.List as List; open List using (List)
open import Data.Unit hiding (poset; _≤_)
open import Function
open import Data.Maybe
open import Data.Product.Relation.Binary.Lex.Strict
open import Data.Product.Relation.Binary.Pointwise.NonDependent
import Relation.Binary.Construct.On as On

------------------------------------------------------------------------
-- Monotone functions

MonoFun : Set
MonoFun = poset ⇒-Poset poset

------------------------------------------------------------------------
-- Memo tables

-- Indices and keys used by the memo table.

Index : Set
Index = Position × MonoFun × Result

data MemoTableKey : Index -> Set where
  key : forall {f r} (key : Key f r) pos -> MemoTableKey (pos , f , r)

-- Input strings of a certain maximum length.

Input≤ : Position -> Set
Input≤ pos = ∃ \pos′ -> pos′ ≤ pos × Input pos′

-- Memo table values.

Value : Index -> Set
Value (pos , f , r) = List (⟦ r ⟧ × Input≤ (fun f pos))

-- Shuffles the elements to simplify defining equality and order
-- relations for the keys.

shuffle : ∃ MemoTableKey -> Position × ∃₂ Key
shuffle ((pos , f , r) , key k .pos) = (pos , f , r , k)

-- Equality and order.

Eq : Rel (∃ MemoTableKey) _
Eq = Pointwise _≡_ _≈'_  on  shuffle

Lt : Rel (∃ MemoTableKey) _
Lt = ×-Lex _≡_ _<P_ _<_  on  shuffle

isOrdered : IsStrictTotalOrder Eq Lt
isOrdered = On.isStrictTotalOrder shuffle
              (×-isStrictTotalOrder posOrdered keyOrdered)

indicesEqual′ : Eq =[ proj₁ ]⇒ _≡_
indicesEqual′ {((_ , _ , _) , key _ ._)}
              {((_ , _ , _) , key _ ._)} (eq₁ , eq₂) =
  cong₂ _,_ eq₁ (cong₂ _,_ (funsEqual eq₂) (resultsEqual eq₂))

open Map isOrdered (\{k₁} {k₂} -> indicesEqual′ {k₁} {k₂}) Value

{-
------------------------------------------------------------------------
-- Parser monad

-- The parser monad is built upon a list monad, for backtracking, and
-- two state monads. One of the state monads stores a memo table, and
-- is unaffected by backtracking. The other state monad, which /is/
-- affected by backtracking, stores the remaining input string.

-- The memo table state monad.

module MemoState = RawMonadState (StateMonadState MemoTable)

-- The list monad.

module List = RawMonadPlus List.ListMonadPlus

-- The inner monad (memo table plus list).

module IM where

  Inner : Set -> Set
  Inner R = State MemoTable (List R)

  InnerMonadPlus : RawMonadPlus Inner
  InnerMonadPlus = record
    { monadZero = record
      { monad = record
        { return = \x -> return (List.return x)
        ; _>>=_  = \m f -> List.concat <$> (List.mapM monad f =<< m)
        }
      ; ∅ = return List.∅
      }
    ; _∣_ = \m₁ m₂ -> List._∣_ <$> m₁ ⊛ m₂
    }
    where
    open MemoState

  InnerMonadState : RawMonadState MemoTable Inner
  InnerMonadState = record
    { monad = RawMonadPlus.monad InnerMonadPlus
    ; get   = List.return <$> get
    ; put   = \s -> List.return <$> put s
    }
    where open MemoState

  open RawMonadPlus  InnerMonadPlus  public
  open RawMonadState InnerMonadState public
    using (get; put; modify)

-- The complete parser monad.

module PM where

  P : MonoFun -> Set -> Set
  P f A = forall {n} -> Input n -> IM.Inner (A × Input≤ (fun f n))

  -- Memoises the computation, assuming that the key is sufficiently
  -- unique.

  memoise : forall {f r} -> Key f r -> P f ⟦ r ⟧ -> P f ⟦ r ⟧
  memoise k p {pos} xs =
    let open IM in helper =<< lookup k′ <$> get
    where
    i = (pos , _)

    k′ : MemoTableKey i
    k′ = key k pos

    helper : Maybe (Value i) -> State MemoTable (Value i)
    helper (just ris) = return ris  where open MemoState
    helper nothing    = p xs                   >>= \ris ->
                        modify (insert k′ ris) >>
                        return ris
      where open MemoState

  -- Other monadic operations.

  return : forall {A} -> A -> P idM A
  return a = \xs -> IM.return (a , _ , refl , xs)

  _>>=_ : forall {A B f g} -> P f A -> (A -> P g B) -> P (g ∘M f) B
  _>>=_ {g = g} m₁ m₂ xs =
    m₁ xs ⟨ IM._>>=_ ⟩ \ays ->
    let a  = proj₁ ays
        le = proj₁ $ proj₂ $ proj₂ ays
        ys = proj₂ $ proj₂ $ proj₂ ays in
    fix le ⟨ IM._<$>_ ⟩ m₂ a ys
    where
    lemma : forall {i j k} -> j ≤ k -> i ≤ fun g j -> i ≤ fun g k
    lemma j≤k i≤gj = trans i≤gj (monotone g j≤k)

    fix : forall {A i j} -> i ≤ j ->
          A × Input≤ (fun g i) ->
          A × Input≤ (fun g j)
    fix le = map-× id (map-Σ id (map-× (lemma le) id))

  ∅ : forall {A} -> P idM A
  ∅ = const IM.∅

  _∣_ : forall {A f} -> P f A -> P f A -> P f A
  m₁ ∣ m₂ = \xs -> IM._∣_ (m₁ xs) (m₂ xs)

  put : forall {n} -> Input n -> P (constM n) ⊤
  put xs = \_ -> IM.return (_ , _ , refl , xs)

  modify : forall {A f} ->
           (forall {n} -> Input n -> A × Input (fun f n)) ->
           P f A
  modify g xs = IM.return (proj₁ gxs , _ , refl , proj₂ gxs)
    where gxs = g xs
-}
