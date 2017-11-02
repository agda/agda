
-- Note: out of order true and false. Confuses the
-- values if we mess up and compile it to a fresh
-- datatype instead of Haskell Bool.
data Two : Set where tt ff : Two

{-# BUILTIN BOOL Two #-}
{-# BUILTIN FALSE ff #-}
{-# BUILTIN TRUE  tt #-}

-- Note: out of order nil and cons. Causes segfault
-- if we mess up and compile it to a fresh datatype
-- instead of Haskell lists.
data List {a} (A : Set a) : Set a where
  _∷_ : A → List A → List A
  []  : List A

{-# BUILTIN LIST List #-}

postulate
  String : Set
  Char : Set

{-# BUILTIN STRING String #-}
{-# BUILTIN CHAR   Char #-}

primitive
  primStringToList   : String → List Char
  primStringFromList : List Char → String
  primStringEquality : String → String → Two

drop1 : {A : Set} → List A → List A
drop1 (x ∷ xs) = xs
drop1 [] = []

postulate
  drop1' : List Char → List Char
{-# COMPILE GHC drop1' = drop 1 #-}

onList : (List Char → List Char) → String → String
onList f s = primStringFromList (f (primStringToList s))

postulate
  _==_ : String → String → Two
{-# COMPILE GHC _==_ = (==) #-}

show : Two → String
show tt = onList drop1  "TRUE"
show ff = onList drop1' "FALSE"

record One : Set where
{-# COMPILE GHC One = data () (()) #-}

postulate IO : Set → Set
{-# BUILTIN IO IO #-}
{-# COMPILE GHC IO = type IO #-}

{-# FOREIGN GHC import qualified Data.Text.IO #-}

postulate putStrLn : String → IO One
{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}

postulate _>>_ : IO One → IO One → IO One
{-# COMPILE GHC _>>_ = (>>) #-}

main : IO One
main = do
  putStrLn (show ("foo" == "bar"))
  putStrLn (show ("foo" == "foo"))
