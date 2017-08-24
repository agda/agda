-- Andreas, 2017-08-24, issue #2717, reported by m0davis
--
-- Internal error in DisplayForm.hs triggered by -v 100.
-- Regression introduced by #2590

{-# OPTIONS -v tc:100 #-} -- KEEP

module _ (A : Set) where

module M (_ : Set) where
  data D (n : Set) : Set where
    d : D n

open M A

{-
displayForm for Issue2717.M.D: context = [CtxId 84,CtxId 83,CtxId 0], dfs = [Local Issue2717 (Display {dfFreeVars = 0, dfPats = [Apply ru(Var 1 []),Apply ru(Var 1 [])], dfRHS = DTerm (Def Issue2717._.D [Apply ru(Var 0 [])])})]
name        : Issue2717.M.D
displayForms: [Display {dfFreeVars = 0, dfPats = [Apply ru(Var 3 []),Apply ru(Var 3 [])], dfRHS = DTerm (Def Issue2717._.D [Apply ru(Var 2 [])])}]
arguments   : [Apply ru(Var 1 []),Apply ru(Var 1 []),Apply ru(Var 0 [])]
matches     : []
result      : Nothing

  restored = Issue2717 : Wk 1 IdS
             Issue2717.M : Wk 1 IdS
             Issue2717.M.D : Wk 1 IdS
             Issue2717._ : Wk 1 IdS
             Issue2717._.D : Wk 1 IdS
  restored = Issue2717 : IdS
             Issue2717.M : IdS
             Issue2717.M.D : IdS
             Issue2717._ : IdS
             Issue2717._.D : IdS
Refining polarity with type  {A = A₁ : Set} {n : Set} → M.D A₁ n
Refining polarity with type (raw):  El {_getSort = Type (Max [ClosedLevel 1]), unEl = Pi ru{El {_getSort = Type (Max [ClosedLevel 1]), unEl = Sort (Type (Max []))}} (Abs "A" El {_getSort = Type (Max [ClosedLevel 1]), unEl = Pi ru{El {_getSort = Type (Max [ClosedLevel 1]), unEl = Sort (Type (Max []))}} (Abs "n" El {_getSort = Type (Max []), unEl = Def Issue2717.M.D [Apply ru(Var 1 []),Apply ru(Var 1 []),Apply ru(Var 0 [])]})})}
updatingModuleParameters
  sub = Wk 1 IdS
  cxt (last added last in list) = A A
  old = Issue2717 : IdS
        Issue2717.M : IdS
        Issue2717.M.D : IdS
        Issue2717._ : IdS
        Issue2717._.D : IdS

  new = Issue2717 : Wk 1 IdS
        Issue2717.M : Wk 1 IdS
        Issue2717.M.D : Wk 1 IdS
        Issue2717._ : Wk 1 IdS
        Issue2717._.D : Wk 1 IdS
updatingModuleParameters
  sub = Wk 1 IdS
  cxt (last added last in list) = A A n
 -- -}
