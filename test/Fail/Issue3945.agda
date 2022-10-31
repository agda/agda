{-# OPTIONS --cohesion #-}

module _ where

data Flat (@♭ A : Set) : Set where
  flat : @♭ A → Flat A

-- the lambda cohesion annotation must match the domain.
into : {@♭ A : Set} → A → Flat A
into = λ (@♭ a) → flat a
