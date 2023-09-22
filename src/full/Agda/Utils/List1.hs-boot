module Agda.Utils.List1 where

import qualified Data.List.NonEmpty (NonEmpty)

type List1 = Data.List.NonEmpty.NonEmpty

groupOn :: Ord b => (a -> b) -> [a] -> [List1 a]
