module TelescopingLet where

module Star where
  ★ : Set₁
  ★ = Set

  ★₁ : Set₂
  ★₁ = Set₁

module MEndo (open Star) (A : ★) where
  Endo : ★
  Endo = A → A

module Batch1 where
  f : (let ★ = Set) (A : ★) → A → A
  f A x = x

  g : (let ★ = Set
           Endo = λ A → A → A) (A : ★) → Endo A
  g = f

  h : (open Star) (A : ★) → A → A
  h = g

module N (open Star) (A : ★) (open MEndo A) (f : Endo) where
  B : ★
  B = A
  f' : Endo
  f' = f

-- module N can be desugared as follows:

module _ where
  open Star
  module _ (A : ★) where
    open MEndo A
    module N' (f : Endo) where
      B : ★
      B = A
      f' : Endo
      f' = f

-- Here are instantiations of N and its desugaring:

f'1 = f'
  where
    postulate A : Set
              f : A → A
    open N A f

f'2 = f'
  where
    postulate A : Set
              f : A → A
    open N' A f

data ⊥ : Set where

module Batch2 where
  f = λ (let ★ = Set) (A : ★) (x : A) → x

  g = λ (open Star) (A : ★) (x : A) → x

  h0 = let open Star in
       λ (A : ★) →
       let module MA = MEndo A in
       let open MA in
       λ (f : Endo) →
       f

  h1 = let open Star in
       λ (A : ★) →
       let open MEndo A in
       λ (f : Endo) →
       f

  h = λ (open Star) (A : ★) (open MEndo A) (f : Endo) → f

module Batch3 where
  e1 : (let ★ = Set) → ★
  e1 = ⊥

  e2 = λ (let ★ = Set) → ★

  e3 = λ (open Star) → ★

  -- "λ (open M es) → e" is an edge case which behaves like "let open M es in e"
