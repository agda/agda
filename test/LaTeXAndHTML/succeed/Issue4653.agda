module _ where -- The top-level module does not count.

module _ where
  private postulate A : Set -- 1.A

module _ where
  private postulate A : Set -- 2.A

module M (_ : Set₁) where -- {mod}M
  module _ where
    private module M₁ where -- {mod}M.3.M₁
    module M₂ where -- {mod}M.M₂
      module _ where
        private postulate A : Set -- M.3.M₂.4.A
    private module M₃ where -- {mod}M.3.M₃
      module _ where
        postulate A : Set -- M.3.M₃.5.A
  module _ where
    module _ where
      module M₃ where -- {mod}M.M₃
        postulate A : Set -- M.M₃.A

B : Set -- B
B = A
  where
  postulate A : Set -- 8.A

C : Set -- C
C = A
  module C where -- {mod}C
  postulate A : Set -- C.A

private module _ where
  postulate A′ : Set -- 9.A′

module _ where
  variable A : Set -- A

module _ where private
  record R : Set₁ where -- 11.R
    constructor c -- {con}11.R.c
    field
      c : Set -- 11.R.c

private module _ where
  record R : Set₁ where -- 12.R
    constructor c -- {con}12.R.c
    field
      c : Set -- 12.R.c

    D : Set -- 12.R.D
    D = c

  record R′ : Set where -- 12.R′
    constructor c -- {con}12.R′.c

module _ where private
  data D : Set where -- 13.D
    c : D -- {con}13.D.c

private module _ where
  data D : Set where -- 14.D
    c : D -- {con}14.D.c

module _ where
  data D′ : Set where -- D′
    c : D′ -- {con}D′.c

pattern c′ = c -- {con}c′
