## MdDontHighlightCode

```agda
module MdDontHighlightCode where
open import Agda.Builtin.String
```

### Marisa

> Sure, but you're still just a tanuki, right?
> The kind that drums on their bellies on the night of the full moon, right?

```agda
module TenDesires where
  record Marisa : Set where
    constructor MkSasa
    field
```

### Mamizou

> You are making light of us, are you not? What do you call yourself?

```agda
      name : String
```

### Marisa

> I'm Reimu Hakurei!

```agda
open TenDesires
open Marisa
_ = MkSasa "Reimu Hakurei"
```

### Mamizou

> Marisa Kirisame, is it? I'll be sure to remember that.
> I intend to take my revenge, so you'd best watch your back on the night of the full moon.
