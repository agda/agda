interleaved mutual
  -- we don't do `data A : Set`
  data A where
    -- you don't have to actually define any constructor to trigger the error, the "where" is enough

  data B where
    b : B
