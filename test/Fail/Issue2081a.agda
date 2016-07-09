-- Andreas, 2016-07-08 testing the access to definitions in where blocks

-- Anonymous where modules do export

pub0 = priv0
  module _ where
    priv0 = Set

works = priv0 -- Should succeed

-- Unnamed where modules don't export

pub = priv
  where
    priv = Set

fail = priv -- Should fail
