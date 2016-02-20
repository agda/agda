open import Common.Prelude renaming (return to foo)

main : IO Unit
main = foo unit
