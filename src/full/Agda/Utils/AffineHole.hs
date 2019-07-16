
-- | Contexts with at most one hole.

module Agda.Utils.AffineHole where



data AffineHole r a
  = ZeroHoles a
      -- ^ A constant term.
  | OneHole (r -> a)
      -- ^ A term with one hole.
  | ManyHoles
      -- ^ A term with many holes (error value).
  deriving (Functor)

instance Applicative (AffineHole r) where
  pure = ZeroHoles

  ZeroHoles f <*> ZeroHoles a = ZeroHoles $ f a
  ZeroHoles f <*> OneHole g   = OneHole $ f . g
  OneHole h   <*> ZeroHoles a = OneHole (`h` a)
  _ <*> _ = ManyHoles

-- NB: @AffineHole r@ is not a monad.
-- @
--   OneHole (h :: r -> a) >>= (k :: a -> AffineHole r b) = _ :: AffineHole r b
-- @
-- We are lacking an @r@ to make use of @h@.
