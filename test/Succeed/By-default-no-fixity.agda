postulate
  ℤ     : Set
  n     : ℤ
  -_ _! : ℤ → ℤ

-- Note that an unrelated prefix/postfix operator can be combined with
-- itself:

ok : ℤ
ok = n ! ! ! !

also-ok : ℤ
also-ok = - - - - - - - n
