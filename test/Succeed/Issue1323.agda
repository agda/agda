data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A → Maybe A

postulate
  String : Set

{-# BUILTIN STRING String #-}

infix 1000 ♯_

postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

infixr 5 _∷_

data Colist (A : Set) : Set where
  []  : Colist A
  _∷_ : (x : A) (xs : ∞ (Colist A)) → Colist A

postulate
  Char : Set

{-# BUILTIN CHAR Char #-}

Costring : Set
Costring = Colist Char

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}

private
 primitive
  primStringAppend   : String → String → String
  primStringToList   : String → List Char
  primStringFromList : List Char → String

infixr 5 _++_

_++_ : String → String → String
_++_ = primStringAppend

toList : String → List Char
toList = primStringToList

fromList : List Char → String
fromList = primStringFromList

fromListToColist : {A : Set} → List A → Colist A
fromListToColist []       = []
fromListToColist (x ∷ xs) = x ∷ ♯ fromListToColist xs

toCostring : String → Costring
toCostring s = fromListToColist (toList s)

------------------------------------------------------------------------

costringToString : Costring → ℕ → Maybe String
costringToString []       _       = just ""
costringToString (x ∷ xs) 0       with ♭ xs
... | []    = just (fromList (x ∷ []))
... | _ ∷ _ = nothing
costringToString (x ∷ xs) (suc n) with costringToString (♭ xs) n
... | nothing  = nothing
... | just xs′ = just (fromList (x ∷ []) ++ xs′)

test0 : costringToString (toCostring "") 0 ≡ just ""
test0 = refl

test1 : costringToString (toCostring "apa") 3 ≡ just "apa"
test1 = refl
