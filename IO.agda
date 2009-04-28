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
  _>>=_  : ∀ {A B} (m : ∞₁ (IO A)) (f : (x : A) → ∞₁ (IO B)) → IO B
  _>>_   : ∀ {A B} (m₁ : ∞₁ (IO A)) (m₂ : ∞₁ (IO B)) → IO B

-- The use of abstract ensures that the run function will not be
-- unfolded infinitely by the type checker.

abstract

  run : ∀ {A} → IO A → Prim.IO A
  run (lift m)   = m
  run (return x) = Prim.return x
  run (m  >>= f) = Prim._>>=_ (run (♭₁ m )) λ x → run (♭₁ (f x))
  run (m₁ >> m₂) = Prim._>>=_ (run (♭₁ m₁)) λ _ → run (♭₁ m₂)

------------------------------------------------------------------------
-- Utilities

-- Because IO A lives in Set₁ I hesitate to define sequence, which
-- would require defining a Set₁ variant of Colist.

mapM : ∀ {A B} → (A → IO B) → Colist A → IO (Colist B)
mapM f []       = return []
mapM f (x ∷ xs) = ♯₁ f x               >>= λ y  →
                  ♯₁ (♯₁ mapM f (♭ xs) >>= λ ys →
                  ♯₁ return (y ∷ ♯ ys))

-- The reason for not defining mapM′ in terms of mapM is efficiency
-- (the unused results could cause unnecessary memory use).

mapM′ : ∀ {A B} → (A → IO B) → Colist A → IO ⊤
mapM′ f []       = return _
mapM′ f (x ∷ xs) = ♯₁ f x >> ♯₁ mapM′ f (♭ xs)

------------------------------------------------------------------------
-- Simple lazy IO (UTF8-based)

getContents : IO Costring
getContents =
  ♯₁ lift Prim.getContents >>= λ s →
  ♯₁ return (Haskell.toColist s)

readFile : String → IO Costring
readFile f =
  ♯₁ lift (Prim.readFile f) >>= λ s →
  ♯₁ return (Haskell.toColist s)

writeFile∞ : String → Costring → IO ⊤
writeFile∞ f s =
  ♯₁ lift (Prim.writeFile f (Haskell.fromColist s)) >>
  ♯₁ return _

writeFile : String → String → IO ⊤
writeFile f s = writeFile∞ f (toCostring s)

putStr∞ : Costring → IO ⊤
putStr∞ s =
  ♯₁ lift (Prim.putStr (Haskell.fromColist s)) >>
  ♯₁ return _

putStr : String → IO ⊤
putStr s = putStr∞ (toCostring s)

putStrLn∞ : Costring → IO ⊤
putStrLn∞ s =
  ♯₁ lift (Prim.putStrLn (Haskell.fromColist s)) >>
  ♯₁ return _

putStrLn : String → IO ⊤
putStrLn s = putStrLn∞ (toCostring s)
