
module Terminal where

open import Base
open import Category
open import Unique
open import Dual
import Iso

module Term (ℂ : Cat) where

  private ℂ' = η-Cat ℂ
  private open module C	= Cat ℂ'
  private open module U = Uniq ℂ'
  private open module I = Iso ℂ'

  Terminal : (A : Obj) -> Set1
  Terminal A = (B : Obj) -> ∃! \(f : B ─→ A) -> True

  toTerminal : {A B : Obj} -> Terminal A -> B ─→ A
  toTerminal term = getWitness (term _)

  terminalIso : {A B : Obj} -> Terminal A -> Terminal B -> A ≅ B
  terminalIso tA tB = iso (toTerminal tB)
			   (toTerminal tA)
			   p q
    where
      p : toTerminal tB ∘ toTerminal tA == id
      p = witnessEqual (tB _) tt tt

      q : toTerminal tA ∘ toTerminal tB == id
      q = witnessEqual (tA _) tt tt

module Init (ℂ : Cat) = Term (η-Cat ℂ op)
    renaming
      ( Terminal    to Initial
      ; toTerminal  to fromInitial
      ; terminalIso to initialIso
      )

