module Issue804 where

mutual

  {-# NON_TERMINATING #-}

  Foo : Set
  Foo = Foo

-- WAS: The pragma above doesn't apply to Foo. An informative error message
-- could be helpful.

-- NOW: The pragma does apply to Foo.
