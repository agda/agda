
data Tm : Set where
  tzero : Tm
  tsucc : Tm → Tm
  tdiff : Tm → Tm → Tm

variable
  m n n' : Tm

data NotZero : Tm → Set where
  nzsucc : NotZero (tsucc n)
  nzdiff : NotZero (tdiff m n)

data Equal : Tm → Tm → Set where
  esucc : NotZero n → Equal (tsucc (tdiff tzero n)) n
  ediff : Equal n n' → Equal (tdiff m n) (tdiff m n')

data Foo : Tm → Set where
  fleft : Foo m → Foo (tdiff m n)
  frght : Foo n → Foo (tdiff m (tsucc n))

foo : Foo n → Equal n n' → Foo n'
foo (fleft f) e = {!!}
foo (frght (frght f)) (ediff (esucc nz)) = {!nz!} -- case-split on nz replaces nz with nzsucc
