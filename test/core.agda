
test.id : (A:Set) -> (x:A) -> A
test.id A x = x

nat.plus : (x:Nat) -> (y:Nat) -> Nat
nat.plus (nat.suc x) y = nat.suc (nat.plus x y)
nat.plus nat.zero y = y

