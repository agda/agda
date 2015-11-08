-- Andreas, 2012-11-18 see issue 761
module AbstractMutual where

module MA where

  mutual
    abstract -- accepted

      S : Set₁
      S = T

      T : Set₁
      T = Set

module AM where

  abstract -- rejected before, should also be accepted
    mutual

      S : Set₁
      S = T

      T : Set₁
      T = Set
