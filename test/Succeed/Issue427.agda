module Issue427 where

data T : Set where
  tt : T

test = (λ {s : T} {t : T} → t) {tt} {tt}


f : {s t : T} → T
f = tt

test₂ = (let x = tt in λ {s : T} {t : T} → x) {tt} {tt}

