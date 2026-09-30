
postulate
  T     : Set
  pre   : (T → T) → T
  pre!_ : (T → T) → T
  _post : T → Set
  _+_   : T → T → T
  _>>=_ : T → (T → T) → T

infix 5 pre!_ _>>=_
infix 4 _post
infixl 3 _+_

-- add parens
test-1a : Set
test-1a = {!pre λ x → x!} post

-- no parens
test-1b : Set
test-1b = {!pre (λ x → x)!} post

-- add parens
test-1c : Set
test-1c = {!pre! λ x → x!} post

-- no parens
test-1d : Set
test-1d = {!pre! (λ x → x)!} post

-- add parens
test-1e : T → Set
test-1e e = {!e >>= λ x → x!} post

-- no parens
test-1f : T → Set
test-1f e = {!e >>= (λ x → x)!} post

-- add parens
test-2a : Set
test-2a = pre {!λ x → x!} post

-- add parens
test-2b : Set
test-2b = pre! {!λ x → x!} post

-- no parens
test-3a : T
test-3a = pre {!λ x → x!}

-- no parens
test-3b : T
test-3b = pre! {!λ x → x!}

-- no parens
test-4a : T → T
test-4a e = e + {!pre λ x → x!}

-- no parens
test-4b : T → T
test-4b e = e + {!pre! λ x → x!}
