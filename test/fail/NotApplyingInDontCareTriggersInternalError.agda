-- Andreas, 2011-10-02
module NotApplyingInDontCareTriggersInternalError where
import Common.Irrelevance  

postulate 
  Val : Set
  App : Val -> Val -> Val -> Set

Rel = Val -> Val -> Set

Transitive : Rel → Set
Transitive R = ∀ {t1 t2 t3} → R t1 t2 → R t2 t3 → R t1 t3

postulate
  LeftReflexive : Rel → Set
  RightReflexive : Rel → Set

record PP (R : Rel) : Set where
  constructor pp
  field
    .leftRefl  : LeftReflexive R
    .rightRefl : RightReflexive R
    .trans     : Transitive R
open PP public

record Those (P : Val → Set)(R : Rel)(P' : Val → Set) : Set where
  constructor those
  field
    B    : Val
    B'   : Val 
    PB   : P B
    PB'  : P' B'
    RBB' : R B B'

Fam : Rel → Set1
Fam AA = ∀ {a a'} → .(AA a a') → Rel

FamTrans : {AA : Rel}.(TA : Transitive AA)(FF : Fam AA) → Set
FamTrans {AA = AA} TA FF = ∀ {a1 a2 a3}(a12 : AA a1 a2)(a23 : AA a2 a3) →
  ∀ {b1 b2 b3}(b12 : FF a12 b1 b2)(b23 : FF a23 b2 b3) →
  FF (TA a12 a23) b1 b3

Π : (AA : Rel) → Fam AA → Rel
Π AA FF g g' = ∀ {a a'} → .(a≼a' : AA a a') → 
  Those (App g a) (FF a≼a') (App g' a')

ΠTrans : {AA : Rel}(PA : PP AA){FF : Fam AA}(TF : FamTrans {AA = AA} (trans PA) FF) →
  Transitive (Π AA FF)
ΠTrans (pp leftRefl rightRefl trans) TF f12 f23 a≼a' with (leftRefl a≼a') 
... | a≼a with f12 a≼a | f23 a≼a' 
ΠTrans (pp leftRefl rightRefl trans) TF f12 f23 a≼a' | a≼a | those b1 b2 app1 app2 b1≼b2 | those b2' b3 app2' app3 b2'≼b3 = those b1 b3 app1 app3 ?

-- This should not give the internal error:
--
--   An internal error has occurred. Please report this as a bug.
--   Location of the error: src/full/Agda/TypeChecking/Substitute.hs:50
--
-- Instead it should complain that
--
--   Variable leftRefl is declared irrelevant, so it cannot be used here
--   when checking that the expression leftRefl a≼a' has type
--   _141 leftRefl rightRefl trans TF f12 f23 a≼a'