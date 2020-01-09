
-- | Contexts with at most one hole.

module Agda.Utils.AffineHole where



data AffineHole r a
  = ZeroHoles a
      -- ^ A constant term.
  | OneHole (r -> a) r
      -- ^ A term with one hole and the (old) contents.
  | ManyHoles
      -- ^ A term with many holes (error value).
  deriving (Functor)

instance Applicative (AffineHole r) where
  pure = ZeroHoles

  ZeroHoles f <*> ZeroHoles a = ZeroHoles $ f a
  ZeroHoles f <*> OneHole g y = OneHole (f . g) y
  OneHole h x <*> ZeroHoles a = OneHole (`h` a) x
  _ <*> _ = ManyHoles

-- NB: @AffineHole r@ is not a monad.
-- @
--   OneHole (h :: r -> a) >>= (k :: a -> AffineHole r b) = _ :: AffineHole r b
-- @
-- We are lacking an @r@ to make use of @h@.
