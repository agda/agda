-- Andreas, 2015-10-28 Issue 1407
-- (Issue 1023 raised its ugly head again!)

{-# OPTIONS -v term.with.inline:30 #-} --KEEP! Triggered bug on agda-2.4.2.5.
-- {-# OPTIONS -v term.with.inline:70 #-}
-- {-# OPTIONS -v tc.with.display:30 #-}

record _×_ (A B : Set) : Set where
  constructor pair
  field fst : A
        snd : B
open _×_

data Unit : Set where
  unit : Unit

data List (A : Set) : Set where
  _∷_ : A → List A → List A

map : ∀ A B → (A → B) → List A → List B
map A B f (x ∷ xs) = f x ∷ map A B f xs

record Setoid : Set₁ where
  field Carrier : Set
open Setoid

module Assoc (Key : Setoid) (_ : Set) where -- FAILS
-- module Assoc (_ : Set) (Key : Setoid) where -- WORKS

  data _∈_ (x : Carrier Key) : List (Carrier Key) → Set where
    here  : ∀ xs → Unit → x ∈ xs
    there : ∀ {xs} → x ∈ xs

  postulate
    foo : Carrier Key → Carrier Key → Unit

  lem : (p : Carrier Key × Unit)
      → (ps : List (Carrier Key × Unit))
      → fst p ∈ map (Carrier Key × Unit) (Carrier Key) fst ps
      → Set
  lem (pair k v) ((pair k' v') ∷ ps) (here .(k' ∷ map (Carrier Key × Unit) (Carrier Key) fst ps) u) with foo k k'
  ... | unit = Unit
  lem p (_ ∷ ps) there = lem p ps there -- to force termination checking

--     7   6       5 4        3  2     1              7       0
-- lem Key _ (pair k v) (pair k' v') ∷ ps) (here .(...Key...) u)
--          8   7 6 5   4         3 2  1  0
-- lem-with Key _ k k' (w = unit) v v' ps u = Unit
{-
inlinedClauses (raw)
  QNamed {qname = Issue1407.Assoc.lem, qnamed = Clause
  { clauseRange = /home/abel/agda/test/bugs/Issue1407.agda:40,3-13
  , clauseTel =
    ExtendTel (Def Issue1407.Setoid []) (Abs "Key"
    ExtendTel (Sort (Type (Max []))) (Abs "_"
    ExtendTel (Var 1 [Proj Issue1407.Setoid.Carrier]}) (Abs "k"
    ExtendTel (Var 2 [Proj Issue1407.Setoid.Carrier]}) (Abs "k'"
    ExtendTel (Def Issue1407.Unit []}) (Abs "v"
    ExtendTel (Def Issue1407.Unit []}) (Abs "v'"
    ExtendTel (Def Issue1407.List [Apply []r(Def Issue1407._×_ [Apply []r(Var 5 [Proj Issue1407.Setoid.Carrier]),Apply []r(Def Issue1407.Unit [])])]}) (Abs "ps"
    ExtendTel (Def Issue1407.Unit []}) (Abs "u"
    EmptyTel))))))))
  , clausePerm = x0,x1,x2,x3,x4,x5,x6,x7,x8 -> x0,x1,x2,x4,x3,x5,x6,x8
  , namedClausePats =
    [[]r(VarP "Key")
    ,[]r(VarP "x")
    ,[]r(ConP Issue1407._×_._,_(inductive)[Issue1407._×_.fst,Issue1407._×_.snd] (ConPatternInfo {conPRecord = Nothing, conPType = Nothing}) [[]r(VarP "k"),[]r(VarP "v")])
    ,[]r(ConP Issue1407.List._∷_(inductive)[] (ConPatternInfo {conPRecord = Nothing, conPType = Nothing}) [[]r(ConP Issue1407._×_._,_(inductive)[Issue1407._×_.fst,Issue1407._×_.snd] (ConPatternInfo {conPRecord = Nothing, conPType = Nothing}) [[]r(VarP "k'"),[]r(VarP "v'")]),[]r(VarP "ps")])
    ,[]r(ConP Issue1407.Assoc._∈_.here(inductive)[] (ConPatternInfo {conPRecord = Nothing, conPType = Nothing})
      [[]r{DotP (Con Issue1407.List._∷_(inductive)[]
        [[]r(Var 4 [])
        ,[]r(Def Issue1407.map
          [Apply []r{Def Issue1407._×_ [Apply []r(Def Issue1407.Assoc._.Carrier [Apply []r(Con Issue1407.Unit.unit(inductive)[] []),Apply []r(Var 3 [])])
                                       ,Apply []r(Def Issue1407.Unit [])]}
          ,Apply []r{Def Issue1407.Assoc._.Carrier [Apply []r(Con Issue1407.Unit.unit(inductive)[] [])
                                                   ,Apply []r(Var 3 [])]}
          ,Apply []r(Lam (ArgInfo {argInfoHiding = NotHidden, argInfoRelevance = Relevant, argInfoColors = []}) (Abs "r" Var 0 [Proj Issue1407._×_.fst]))
          ,Apply []r(Var 1 [])
          ])
        ])}
      ,[]r(VarP "u")
      ])
    ,[]r(ConP Issue1407.Unit.unit(inductive)[] (ConPatternInfo {conPRecord = Nothing, conPType = Nothing}) [])
    ]
  , clauseBody = Bind (Abs "h8" Bind (Abs "h7" Bind (Abs "h6" Bind (Abs "h5" Bind (Abs "h4" Bind (Abs "h3" Bind (Abs "h2" Bind (Abs "h1" Bind (Abs "h0" Body (Def Issue1407.Unit [])))))))))), clauseType = Nothing}}

-}
