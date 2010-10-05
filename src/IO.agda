------------------------------------------------------------------------
-- IO
------------------------------------------------------------------------

{-# OPTIONS --no-termination-check #-}

module IO where

open import Coinduction
open import Data.Unit
open import Data.String
open import Data.Colist
import Foreign.Haskell as Haskell
import IO.Primitive as Prim

------------------------------------------------------------------------
-- The IO monad

-- One cannot write "infinitely large" computations with the
-- postulated IO monad in IO.Primitive without turning off the
-- termination checker (or going via the FFI, or perhaps abusing
-- something else). The following coinductive deep embedding is
-- introduced to avoid this problem. Possible non-termination is
-- isolated to the run function below.

infixl 1 _>>=_ _>>_

data IO : Set → Set₁ where
  lift   : ∀ {A} (m : Prim.IO A) → IO A
  return : ∀ {A} (x : A) → IO A
  _>>=_  : ∀ {A B} (m : ∞ (IO A)) (f : (x : A) → ∞ (IO B)) → IO B
  _>>_   : ∀ {A B} (m₁ : ∞ (IO A)) (m₂ : ∞ (IO B)) → IO B

-- The use of abstract ensures that the run function will not be
-- unfolded infinitely by the type checker.

abstract

  run : ∀ {A} → IO A → Prim.IO A
  run (lift m)   = m
  run (return x) = Prim.return x
  run (m  >>= f) = Prim._>>=_ (run (♭ m )) λ x → run (♭ (f x))
  run (m₁ >> m₂) = Prim._>>=_ (run (♭ m₁)) λ _ → run (♭ m₂)

------------------------------------------------------------------------
-- Utilities

-- Because IO A lives in Set₁ I hesitate to define sequence, which
-- would require defining a Set₁ variant of Colist.

mapM : {A B : Set} → (A → IO B) → Colist A → IO (Colist B)
mapM f []       = return []
mapM f (x ∷ xs) = ♯ f x              >>= λ y  →
                  ♯ (♯ mapM f (♭ xs) >>= λ ys →
                  ♯ return (y ∷ ♯ ys))

-- The reason for not defining mapM′ in terms of mapM is efficiency
-- (the unused results could cause unnecessary memory use).

mapM′ : {A B : Set} → (A → IO B) → Colist A → IO ⊤
mapM′ f []       = return _
mapM′ f (x ∷ xs) = ♯ f x >> ♯ mapM′ f (♭ xs)

------------------------------------------------------------------------
-- Simple lazy IO

-- Note that the semantics of these functions depends on the version
-- of the Haskell base library. If the version is 4.2.0.0 (or later?),
-- then the functions use the character encoding specified by the
-- locale. For older versions of the library (going back to at least
-- version 3) the functions use ISO-8859-1.

getContents : IO Costring
getContents =
  ♯ lift Prim.getContents >>= λ s →
  ♯ return (Haskell.toColist s)

readFile : String → IO Costring
readFile f =
  ♯ lift (Prim.readFile f) >>= λ s →
  ♯ return (Haskell.toColist s)

writeFile∞ : String → Costring → IO ⊤
writeFile∞ f s =
  ♯ lift (Prim.writeFile f (Haskell.fromColist s)) >>
  ♯ return _

writeFile : String → String → IO ⊤
writeFile f s = writeFile∞ f (toCostring s)

appendFile∞ : String → Costring → IO ⊤
appendFile∞ f s =
  ♯ lift (Prim.appendFile f (Haskell.fromColist s)) >>
  ♯ return _

appendFile : String → String → IO ⊤
appendFile f s = appendFile∞ f (toCostring s)

putStr∞ : Costring → IO ⊤
putStr∞ s =
  ♯ lift (Prim.putStr (Haskell.fromColist s)) >>
  ♯ return _

putStr : String → IO ⊤
putStr s = putStr∞ (toCostring s)

putStrLn∞ : Costring → IO ⊤
putStrLn∞ s =
  ♯ lift (Prim.putStrLn (Haskell.fromColist s)) >>
  ♯ return _

putStrLn : String → IO ⊤
putStrLn s = putStrLn∞ (toCostring s)
