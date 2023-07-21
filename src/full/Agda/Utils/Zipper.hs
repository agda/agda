{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Utils.Zipper where


class Zipper z where
  type Carrier z
  type Element z
  firstHole :: Carrier z -> Maybe (Element z, z)
  plugHole  :: Element z -> z -> Carrier z
  nextHole  :: Element z -> z -> Either (Carrier z) (Element z, z)

data ListZipper a = ListZip [a] [a]
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Zipper (ListZipper a) where
  type Carrier (ListZipper a) = [a]
  type Element (ListZipper a) = a
  firstHole (x : xs)               = Just (x, ListZip [] xs)
  firstHole []                     = Nothing
  plugHole x (ListZip ys zs)       = reverse ys ++ x : zs
  nextHole x (ListZip ys [])       = Left (reverse (x : ys))
  nextHole x (ListZip ys (z : zs)) = Right (z, ListZip (x : ys) zs)

data ComposeZipper f g = ComposeZip f g

instance (Zipper f, Zipper g, Element f ~ Carrier g) => Zipper (ComposeZipper f g) where
  type Carrier (ComposeZipper f g) = Carrier f
  type Element (ComposeZipper f g) = Element g
  firstHole c1 = do
    (c2, z1) <- firstHole c1
    go c2 z1
    where
      go c2 z1 =
        case firstHole c2 of
          Nothing -> case nextHole c2 z1 of
            Left{} -> Nothing
            Right (c2', z1') -> go c2' z1'
          Just (x, z2) -> Just (x, ComposeZip z1 z2)
  plugHole x (ComposeZip z1 z2) = plugHole (plugHole x z2) z1
  nextHole x (ComposeZip z1 z2) =
    case nextHole x z2 of
      Right (y, z2') -> Right (y, ComposeZip z1 z2')
      Left c2        -> go c2 z1
        where
          go c2 z1 =
            case nextHole c2 z1 of
              Right (c2', z1') ->
                case firstHole c2' of
                  Nothing       -> go c2' z1'
                  Just (x, z2') -> Right (x, ComposeZip z1' z2')
              Left c1 -> Left c1
