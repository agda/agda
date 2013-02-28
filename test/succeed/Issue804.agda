module Issue804 where

mutual

  {-# NO_TERMINATION_CHECK #-}

  Foo : Set
  Foo = Foo

-- WAS: The pragma above doesn't apply to Foo. An informative error message
-- could be helpful.

-- NOW: The pragma does apply to Foo.
