
postulate
  A   : Set
  _+_ : A → A → A

f₁ : A → A → A
f₁ x y = {!_+ x!}  -- ? + x

f₂ : A → A → A
f₂ x y = {!x +_!}  -- x + ?

f₃ : A → A → A
f₃ x = {!_+ x!}  -- λ section → section + x

f₄ : A → A → A
f₄ x y = {!λ z → z + x!} -- ? + x

f₅ : A → A → A
f₅ x y = {!λ a b → b + x!}  -- ? + x

f₆ : A → A → A
f₆ x y = {!λ a → a + (a + x)!} -- (λ a → a + (a + x)) ?

f₇ : A → A → A
f₇ x y = {!λ a → x + (y + a)!}  -- x + (y + ?)

f₈ : A → A → A
f₈ x = {!λ a b → a + b!} -- λ b → ? + b
