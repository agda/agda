-- Andreas, 2014-05-02  Negative fixities allow now.

module _ where

infix -1 _+_
infix 0  _*_

postulate
  _+_ : Set1 → Set2 → Set1
  _*_ : Set2 → Set2 → Set2

test = Set + Set1 * Set1
