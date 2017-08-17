
open import Agda.Builtin.Nat

data Sing : Nat → Set where
  i : (k : Nat) → Sing k

toSing : (n : Nat) → Sing n
toSing n = i n

fun : (n : Nat) → Nat
fun n with toSing n
fun .n       | i n with toSing n
fun .(n + n) | i .n | i n = {!!}
