open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.String
  renaming (primShowNat to show)
open import Agda.Builtin.Reflection
  renaming (bindTC to _>>=_; returnTC to return)

pattern vArg t = arg (arg-info visible relevant) t
pattern var₀ x = var x []

infixr 10 _++_
_++_ = primStringAppend

postulate
  whatever : ∀ {a} {A : Set a} → A

macro
  test1 : Nat → Term → TC _
  test1 n _ =
    extendContext (vArg (quoteTerm Nat)) do
      var₀ i ← quoteTC n where _ → whatever
      m ← unquoteTC {A = Nat} (var₀ 0)
      var₀ j ← quoteTC m where _ → whatever
      extendContext (vArg (quoteTerm Nat)) do
        var₀ k ← quoteTC n where _ → whatever
        var₀ l ← quoteTC m where _ → whatever
        typeError (strErr (show i ++ show k ++ show j ++ show l) ∷ [])

  test2 : Term → TC _
  test2 hole = do
    st ← quoteTC Set
    t ← extendContext (vArg st) do
      v ← unquoteTC {A = Set} (var₀ zero)
      extendContext (vArg (var₀ zero)) do
        _ ← unquoteTC {A = v} (var₀ zero)
        return tt
    u ← quoteTC t
    unify hole u

  test3 : Nat → Term → TC _
  test3 n _ = do
    m      ← extendContext (vArg (quoteTerm Nat)) (return n)
    var₀ i ← quoteTC m where _ → whatever
    typeError (strErr (show i) ∷ [])

  localvar : Term → TC _
  localvar _ = do
    m ← extendContext (vArg (quoteTerm Nat)) (unquoteTC {A = Nat} (var₀ 0))
    typeError (strErr (show m) ∷ [])
