-- Andreas, 2021-04-28, issue #5336
-- data...where is already extensible.

module _ where

module C where
  postulate
    Name QName : Set

variable
  x  y  : C.Name
  xs ys : C.QName

interleaved mutual

  -- Scope of a declaration.

  data Scope : Set
  variable
    sc sc' : Scope

  -- Declarations in a scope.

  data Decls (sc : Scope) : Set
  variable
    ds₀ ds ds' : Decls sc

  -- A definition in a scope.
  -- So far, we can only define modules, which hold declarations.

  data Val : (sc : Scope) → Set

  -- We use letter v ("value") for definitions.

  variable
    v v' : Val sc

  -- A well-scoped name pointing to its definition.

  data Name : (sc : Scope) → Val sc → Set

  variable
    n n' : Name sc v

  -- A well-scoped declaration is one of
  --
  --   * A module definition.
  --   * Importing the declarations of another module via `open`.

  data Decl (sc : Scope) : Set where
    modl : (x : C.Name) (ds : Decls sc) → Decl sc
    opn  : (n : Name sc v)              → Decl sc

  variable
    d d' : Decl sc

  -- A scope is a snoc list of lists of declarations.

  data Scope where
    ε   : Scope

  data Scope where
    _▷_ : (sc : Scope) (ds : Decls sc) → Scope

  -- Lists of declarations are also given in snoc-form.

  data Decls where
    ε   : Decls sc

  data Decls where
    _▷_ : (ds : Decls sc) (d : Decl (sc ▷ ds)) → Decls sc

  data Val where
    -- The content of a module.
    content : (ds : Decls sc) → Val sc
    -- Qualifying a value that is taken from inside module x.
    inside  : (x : C.Name) (v : Val ((sc ▷ ds) ▷ ds')) → Val (sc ▷ (ds ▷ modl x ds'))
    imp     : (n : Name (sc ▷ ds₀) (content ds')) (v : Val ((sc ▷ ds₀) ▷ ds'))
            → Val (sc ▷ (ds₀ ▷ opn n))

  -- Weakning from one scope to an extended scope.

  data _⊆_ : (sc sc' : Scope) → Set

  variable
    τ : sc ⊆ sc'

  -- Weakning by a list of declarations or a single declaration.

  wk1  : sc ⊆ (sc ▷ ds)
  wk01 : (sc ▷ ds) ⊆ (sc ▷ (ds ▷ d))

  -- Weakening a definition.

  data WkVal : (τ : sc ⊆ sc') → Val sc → Val sc' → Set

  variable
    wv wv' wv₀ : WkVal τ v v'

  data WkDecl  (τ : sc ⊆ sc') : Decl  sc → Decl  sc' → Set
  variable
    wd wd' : WkDecl τ d d'

  data WkDecls : (τ : sc ⊆ sc') → Decls sc → Decls sc' → Set
  variable
    wds₀ wds wds' : WkDecls τ ds ds'

  -- Names resolving in a list of declarations.

  data DsName (sc : Scope) : (ds : Decls sc) → Val (sc ▷ ds) → Set -- where
  variable
    nds nds' : DsName sc ds v

  -- Names resolving in a declaration.

  data DName  (sc : Scope) (ds₀ : Decls sc) : (d : Decl (sc ▷ ds₀)) → Val (sc ▷ (ds₀ ▷ d)) → Set where

    modl   : (wds : WkDecls wk01 ds ds')
           → DName sc ds₀ (modl x ds) (content ds')

    inside : (n : DsName (sc ▷ ds₀) ds' v)
           → DName sc ds₀ (modl x ds') (inside x v)

    imp    : (n : Name (sc ▷ ds₀) (content ds'))
             (nds : DsName (sc ▷ ds₀) ds' v)
           → DName sc ds₀ (opn n) (imp n v)

  variable
    nd nd' : DName sc ds d  v

  -- This finally allows us to define names resolving in a scope.

  data DsName where
    here  : (nd  : DName  sc ds d v)                     → DsName sc (ds ▷ d) v
    there : (w : WkVal wk01 v v') (nds : DsName sc ds v) → DsName sc (ds ▷ d) v'

  data Name where
    site   :                      (nds : DsName sc ds v) → Name (sc ▷ ds) v
    parent : (w : WkVal wk1 v v') (n   : Name   sc    v) → Name (sc ▷ ds) v'

  ------------------------------------------------------------------------
  -- Relating entities defined in a scope to their weakenings.

  -- Weakenings are order-preserving embeddings.

  data _⊆_ where
    ε    : ε ⊆ ε
    _▷_  : (τ : sc ⊆ sc') (wds : WkDecls τ ds ds') → (sc ▷ ds) ⊆ (sc' ▷ ds')
    _▷ʳ_ : (τ : sc ⊆ sc') (ds  : Decls sc')        → sc        ⊆ (sc' ▷ ds)

  data WkDecls where
    ε     : WkDecls τ ε ε
    _▷_   : (ws : WkDecls τ ds ds') (wd : WkDecl (τ ▷ ws) d d') → WkDecls τ (ds ▷ d) (ds' ▷ d')
    _▷ʳ_  : (ws : WkDecls τ ds ds') (d  : Decl (_ ▷ ds'))       → WkDecls τ  ds      (ds' ▷ d)

  refl-⊆         : sc ⊆ sc
  wkDecls-refl-⊆ : WkDecls τ ds ds
  wkDecl-refl-⊆  : WkDecl  τ d  d

  wkDecls-refl-⊆ {ds = ε}      = ε
  wkDecls-refl-⊆ {ds = ds ▷ d} = wkDecls-refl-⊆ ▷ wkDecl-refl-⊆

  refl-⊆ {sc = ε}       = ε
  refl-⊆ {sc = sc ▷ ds} = refl-⊆ ▷ wkDecls-refl-⊆

  -- We can now define the singleton weaknings.

  -- By another list of declarations.
  wk1 {ds = ds} = refl-⊆ ▷ʳ ds

  -- By a single declaration.
  wk01 {d = d} = refl-⊆ ▷ (wkDecls-refl-⊆ ▷ʳ d)

  -- Weakning names

  data WkName : (τ : sc ⊆ sc') (wv : WkVal τ v v') → Name sc v → Name sc' v' → Set

  postulate
    wkVal-refl-⊆  : WkVal  τ    v v
    wkName-refl-⊆ : WkName τ wv n n

  data WkDecl where
    modl : (w  : WkDecls τ    ds ds') → WkDecl τ (modl x ds) (modl x ds')
    opn  : (wn : WkName  τ wv n  n' ) → WkDecl τ (opn n)   (opn n')

  wkDecl-refl-⊆ {d = modl x ds} = modl wkDecls-refl-⊆
  wkDecl-refl-⊆ {d = opn n    } = opn {wv = wkVal-refl-⊆} wkName-refl-⊆

  -- We can prove that the identity weaking leaves definitions unchanged.

  data WkVal where
    content : (wds : WkDecls τ ds ds') → WkVal τ (content ds) (content ds')
    inside  : (wv : WkVal ((τ ▷ wds) ▷ wds') v  v' )
            → WkVal (τ ▷ (wds ▷ modl wds')) (inside x v) (inside x v')

  data WkName where
    site   : WkName τ wv (site nds) (site nds')
