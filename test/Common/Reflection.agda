{-# OPTIONS --level-universe #-}

module Common.Reflection where

open import Agda.Builtin.Reflection public renaming
  ( arg-info      to argInfo
  ; function      to funDef
  ; data-type     to dataDef
  ; record-type   to recordDef
  ; agda-sort     to sort
  ; name          to qname
  ; absurd-clause to absurdClause
  ; pat-lam       to extLam
  ; proj          to projP
  ; instance′      to inst
  ; Visibility    to Hiding
  ; Name          to QName)
open import Common.Level
open import Common.Prelude hiding (_>>=_)

pattern defaultModality = modality relevant quantity-ω
pattern vArg x = arg (argInfo visible defaultModality) x
pattern hArg x = arg (argInfo hidden  defaultModality) x
pattern iArg x = arg (argInfo inst    defaultModality) x

Args = List (Arg Term)

data FunDef : Set where
  funDef : Type → List Clause → FunDef

Tactic = Term → TC ⊤

give : Term → Tactic
give v = λ hole → unify hole v

define : Arg QName → FunDef → TC ⊤
define (arg i f) (funDef a cs) =
  bindTC (declareDef (arg i f) a) λ _ →
  defineFun f cs

newMeta : Type → TC Term
newMeta a = checkType unknown a

numberOfParameters : QName → TC Nat
numberOfParameters d =
  bindTC (getDefinition d) λ
  { (dataDef n _) → returnTC n
  ; _ → typeError (strErr "Cannot get parameters of non-data type" ∷ nameErr d ∷ [])
  }

getConstructors : QName → TC (List QName)
getConstructors d =
  bindTC (getDefinition d) λ
  { (dataDef _ cs)  → returnTC cs
  ; (recordDef c _) → returnTC (c ∷ [])
  ; _ → typeError (strErr "Cannot get constructors of non-data or record type" ∷ nameErr d ∷ [])
  }

infixl 1 _>>=_
_>>=_ = bindTC
