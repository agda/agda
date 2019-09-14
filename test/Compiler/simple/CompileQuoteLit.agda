module CompileQuoteLit where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.String renaming (primStringAppend to infixr 6 _&_)
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection renaming (bindTC to infixl 4 _>>=_)
open import Agda.Builtin.IO

variable
  ℓ : Level
  A : Set ℓ

par : String → String
par s = "(" & s & ")"

showList′ : (A → String) → List A → String
showList′ _ [] = "]"
showList′ f (x ∷ []) = f x & "]"
showList′ f (x ∷ xs) = f x & ", " & showList′ f xs

showList : (A → String) → List A → String
showList f xs = "[" & showList′ f xs

{-# TERMINATING #-}
showArgs : (A → String) → List (Arg A) → String
showArg : (A → String) → Arg A → String
showLit : Literal → String
showAbs : Abs Term → String
showSort : Sort → String
showClauses : List Clause → String

show : Term → String
show (var x args) = par ("var " & primShowNat x & " " & showArgs show args)
show (con c args) = par ("con " & primShowQName c & " " & showArgs show args)
show (def f args) = par ("def " & primShowQName f & " " & showArgs show args)
show (lam v t) = par ("λ " & showAbs t)
show (pat-lam cs args) = par ("patlam " & showClauses cs & " " & showArgs show args)
show (pi a b) = par ("Π " & showArg show a & " " & showAbs b)
show (agda-sort s) = par ("sort " & showSort s)
show (lit l) = par ("lit " & showLit l)
show (meta x x₁) = "meta"
show unknown = "unknown"

showSort (set t) = par ("set " & show t)
showSort (lit n) = par ("lit " & primShowNat n)
showSort unknown = "unknown"

showLit (nat n) = par ("nat " & primShowNat n)
showLit (word64 n) = "word64"
showLit (float x) = "float"
showLit (char c) = "char"
showLit (string s) = par ("string " & primShowString s)
showLit (name x) = "name"
showLit (meta x) = "meta"

showAbs (abs s t) = s & " → " & show t

showArgInfo : ArgInfo → String → String
showArgInfo (arg-info visible _) s = s
showArgInfo (arg-info hidden _) s = "{" & s & "}"
showArgInfo (arg-info instance′ _) s = "⦃ " & s & " ⦄"

showArg f (arg h x) = showArgInfo h (f x)
showArgs f = showList (showArg f)

showPat : Pattern → String
showPat (con c ps) = par ("con " & primShowQName c & " " & showArgs showPat ps)
showPat dot = "dot"
showPat (var s) = par ("var " & primShowString s)
showPat (lit l) = par ("lit " & showLit l)
showPat (proj f) = par ("proj " & primShowQName f)
showPat absurd = "()"

showClause : Clause → String
showClause (clause ps t) = par ("clause " & showArgs showPat ps & " " & show t)
showClause (absurd-clause ps) = par ("absurd-clause " & showArgs showPat ps)

showClauses = showList showClause

macro
  q : A → Term → TC ⊤
  q x hole = do
    `x  ← quoteTC x
    ``x ← quoteTC `x
    unify hole ``x

postulate
  putStrLn : String → IO ⊤
{-# FOREIGN GHC import Data.Text.IO #-}
{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}
{-# COMPILE JS putStrLn = function (x) { return function(cb) { process.stdout.write(x + "\n"); cb(0); }; } #-}

some-term : Term
some-term = q (1 + 2)

main : IO ⊤
main = putStrLn (show some-term)
