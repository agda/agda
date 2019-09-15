open import Agda.Builtin.Bool

works : Bool → Bool
works b with b | true
... | b′ | _ = b′

fails : Bool → Bool
fails b with b′ ← b | true
... | _ = b′
