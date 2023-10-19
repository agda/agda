import Issue6931.One as One

module Issue6931.Three (A : Set) where

  module Public
    (open One A)
    (x : B) where

    -- must be empty

  module HasPrivate
    (open One A)
    (x : B) where

    -- or just have private definitions
    private
      postulate
        priv : B
