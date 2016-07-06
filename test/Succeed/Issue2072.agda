
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.String

infixr 4 _>>=_
_>>=_ = bindTC

login : String → String
login "secret" = "access granted"
login _        = "access denied"

macro
  getDef : Name → Term → TC ⊤
  getDef f hole =
    getDefinition f >>= λ def → quoteTC def >>= unify hole

test : Definition
test = getDef login
