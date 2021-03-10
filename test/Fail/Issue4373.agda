
module _ where

import Issue4373.A as A hiding (t)

postulate
  search : ⦃ x : A.T ⦄ → Set

fail : Set
fail = search
