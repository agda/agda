-- Andreas, 2017-05-13, issue reported by nad

module Issue2579 where

open import Common.Bool

open import Issue2579.Import
import Issue2579.Instance Bool true as I
-- without the "as I" the instance is not in scope
-- (and you get a parse error)

theWrapped : {{w : Wrap Bool}} → Bool
theWrapped {{w}} = Wrap.wrapped w

test : Bool
test = theWrapped
