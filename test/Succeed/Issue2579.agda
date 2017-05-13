-- Andreas, 2017-05-13, issue reported by nad

module Issue2579 where

open import Common.Bool

open import Issue2579.Import
import Issue2579.Instance Bool true  -- imports instances

theWrapped : {{w : Wrap Bool}} → Bool
theWrapped {{w}} = Wrap.wrapped w

test : Bool
test = theWrapped
