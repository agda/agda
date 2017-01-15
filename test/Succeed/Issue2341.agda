-- Andreas, 2016-12-15, issue #2341
-- `with` needs to abstract also in sort of target type.

-- {-# OPTIONS -v tc.with:100 #-}

open import Agda.Primitive

data _≡_ {a}{A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

postulate
  equalLevel : (x y : Level) → x ≡ y

id : ∀ {a} {A : Set a} → A → A
id x = x

Works : ∀ β α → Set α → Set β
Works β α with equalLevel α β
Works β .β | refl = id

Coerce : ∀ β α → Set α → Set β
Coerce β α rewrite equalLevel α β = id

-- Should succeed

{-
Set α →{1+β⊔α} Set β
added with function .Issue2341.rewrite-42 of type
  (β α w : Level) → w ≡ β → Set w → Set β

  (β α : Level) → (w : Level) →{1+β⊔α} w ≡ β →{1+β⊔α} Set w →{1+β⊔α} Set β

  raw with func. type = El {_getSort = Inf, unEl =
Pi ru(El {_getSort = Type (Max []), unEl = Def Agda.Primitive.Level []}) (Abs "\946" El {_getSort = Inf, unEl =
Pi ru(El {_getSort = Type (Max []), unEl = Def Agda.Primitive.Level []}) (Abs "\945"
  El {_getSort = Type (Max [Plus 1 (UnreducedLevel (Var 0 [])),Plus 1 (UnreducedLevel (Var 1 []))]), unEl =
Pi ru(El {_getSort = Type (Max []), unEl = Def Agda.Primitive.Level []}) (Abs "w"
  El {_getSort = Type (Max [Plus 1 (UnreducedLevel (Var 1 [])),Plus 1 (UnreducedLevel (Var 2 []))]), unEl =
Pi ru(El {_getSort = Type (Max []), unEl = Def Issue2341._≡_ [Apply ru{Level (Max [])},Apply ru{Def Agda.Primitive.Level []},Apply ru(Var 0 []),Apply ru(Var 2 [])]}) (NoAbs "w"
  El {_getSort = Type (Max [Plus 1 (UnreducedLevel (Var 1 [])),Plus 1 (UnreducedLevel (Var 2 []))]), unEl =
Pi ru(El {_getSort = Type (Max [Plus 1 (UnreducedLevel (Var 0 []))]), unEl = Sort (Type (Max [Plus 0 (UnreducedLevel (Var 0 []))]))}) (NoAbs "_"
  El {_getSort = Type (Max [Plus 1 (UnreducedLevel (Var 2 []))]), unEl =
Sort (Type (Max [Plus 0 (UnreducedLevel (Var 2 []))]))})})})})})}
-}
