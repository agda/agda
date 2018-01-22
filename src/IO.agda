------------------------------------------------------------------------
-- The Agda standard library
--
-- IO
------------------------------------------------------------------------

module IO where

open import Coinduction
open import Data.Unit
open import Data.String
open import Data.Colist
open import Function
import IO.Primitive as Prim
open import Level

------------------------------------------------------------------------
-- The IO monad

-- One cannot write "infinitely large" computations with the
-- postulated IO monad in IO.Primitive without turning off the
-- termination checker (or going via the FFI, or perhaps abusing
-- something else). The following coinductive deep embedding is
-- introduced to avoid this problem. Possible non-termination is
-- isolated to the run function below.

infixl 1 _>>=_ _>>_

data IO {a} (A : Set a) : Set (suc a) where
  lift   : (m : Prim.IO A) → IO A
  return : (x : A) → IO A
  _>>=_  : {B : Set a} (m : ∞ (IO B)) (f : (x : B) → ∞ (IO A)) → IO A
  _>>_   : {B : Set a} (m₁ : ∞ (IO B)) (m₂ : ∞ (IO A)) → IO A

{-# NON_TERMINATING #-}

run : ∀ {a} {A : Set a} → IO A → Prim.IO A
run (lift m)   = m
run (return x) = Prim.return x
run (m  >>= f) = Prim._>>=_ (run (♭ m )) λ x → run (♭ (f x))
run (m₁ >> m₂) = Prim._>>=_ (run (♭ m₁)) λ _ → run (♭ m₂)

------------------------------------------------------------------------
-- Utilities

sequence : ∀ {a} {A : Set a} → Colist (IO A) → IO (Colist A)
sequence []       = return []
sequence (c ∷ cs) = ♯ c                  >>= λ x  →
                    ♯ (♯ sequence (♭ cs) >>= λ xs →
                    ♯ return (x ∷ ♯ xs))

-- The reason for not defining sequence′ in terms of sequence is
-- efficiency (the unused results could cause unnecessary memory use).

sequence′ : ∀ {a} {A : Set a} → Colist (IO A) → IO (Lift ⊤)
sequence′ []       = return _
sequence′ (c ∷ cs) = ♯ c                   >>
                     ♯ (♯ sequence′ (♭ cs) >>
                     ♯ return _)

mapM : ∀ {a b} {A : Set a} {B : Set b} →
       (A → IO B) → Colist A → IO (Colist B)
mapM f = sequence ∘ map f

mapM′ : {A B : Set} → (A → IO B) → Colist A → IO (Lift ⊤)
mapM′ f = sequence′ ∘ map f

------------------------------------------------------------------------
-- Simple lazy IO

-- Note that the functions below produce commands which, when
-- executed, may raise exceptions.

-- Note also that the semantics of these functions depends on the
-- version of the Haskell base library. If the version is 4.2.0.0 (or
-- later?), then the functions use the character encoding specified by
-- the locale. For older versions of the library (going back to at
-- least version 3) the functions use ISO-8859-1.

getContents : IO Costring
getContents = lift Prim.getContents

readFile : String → IO Costring
readFile f = lift (Prim.readFile f)

-- Reads a finite file. Raises an exception if the file path refers to
-- a non-physical file (like "/dev/zero").

readFiniteFile : String → IO String
readFiniteFile f = lift (Prim.readFiniteFile f)

writeFile∞ : String → Costring → IO ⊤
writeFile∞ f s =
  ♯ lift (Prim.writeFile f s) >>
  ♯ return _

writeFile : String → String → IO ⊤
writeFile f s = writeFile∞ f (toCostring s)

appendFile∞ : String → Costring → IO ⊤
appendFile∞ f s =
  ♯ lift (Prim.appendFile f s) >>
  ♯ return _

appendFile : String → String → IO ⊤
appendFile f s = appendFile∞ f (toCostring s)

putStr∞ : Costring → IO ⊤
putStr∞ s =
  ♯ lift (Prim.putStr s) >>
  ♯ return _

putStr : String → IO ⊤
putStr s = putStr∞ (toCostring s)

putStrLn∞ : Costring → IO ⊤
putStrLn∞ s =
  ♯ lift (Prim.putStrLn s) >>
  ♯ return _

putStrLn : String → IO ⊤
putStrLn s = putStrLn∞ (toCostring s)

-- Note that the commands writeFile, appendFile, putStr and putStrLn
-- perform two conversions (string → costring → Haskell list). It may
-- be preferable to only perform one conversion.
