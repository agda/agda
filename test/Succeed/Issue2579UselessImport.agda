-- Andreas, 2025-11-07, UselessImport warning for instantiated import without open.

module _ where

import DummyModule Set Set

-- warning: -W[no]UselessImport
-- An import statement with module instantiation is useless without
-- either an `open' keyword or an `as` binding giving a name to the
-- instantiated module.
