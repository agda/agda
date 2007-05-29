{-# OPTIONS -cpp #-}

module TypeChecking.Rules.Record where

import Control.Monad.Trans

import qualified Syntax.Abstract as A
import Syntax.Common
import Syntax.Internal
import Syntax.Position
import qualified Syntax.Info as Info

import TypeChecking.Monad
import TypeChecking.Substitute
import TypeChecking.Reduce
import TypeChecking.Pretty

import TypeChecking.Rules.Data ( bindParameters, fitsIn )
import TypeChecking.Rules.Term ( isType_ )

import Utils.Size

#include "../../undefined.h"

---------------------------------------------------------------------------
-- * Records
---------------------------------------------------------------------------

checkRecDef :: Info.DefInfo -> QName -> [A.LamBinding] -> [A.Constructor] -> TCM ()
checkRecDef i name ps fields =
  traceCall (CheckRecDef (getRange i) (qnameName name) ps fields) $ do
    t <- instantiateFull =<< typeOfConst name
    bindParameters ps t $ \tel t0 -> do
      s <- case unEl t0 of
	Sort s	-> return s
	_	-> typeError $ ShouldBeASort t0
      gamma <- getContextTelescope
      let m = mnameFromList $ qnameToList name
	  hide (Arg _ x) = Arg Hidden x
	  htel		 = map hide $ telToList tel
	  rect		 = El s $ Def name $ reverse 
			   [ Arg h (Var i [])
			   | (i, Arg h _) <- zip [0..] $ reverse $ telToList gamma
			   ]
	  tel'		 = telFromList $ htel ++ [Arg NotHidden ("r", rect)]

      -- We have to rebind the parameters to make them hidden
      escapeContext (size tel) $ addCtxTel tel' $ do
	reportSDoc "tc.rec.def" 10 $ sep
	  [ text "record section:"
	  , nest 2 $ prettyTCM m <+> (prettyTCM =<< getContextTelescope)
	  ]
	addSection m (size tel')

      -- Check the types of the fields
      ftel <- withCurrentModule m $ checkRecordFields m name tel s [] [] (size fields) fields

      -- Check that the fields fit inside the sort
      telePi ftel t0 `fitsIn` s

      let getName (A.Axiom _ x _)      = x
	  getName (A.ScopedDecl _ [f]) = getName f
	  getName _		       = __IMPOSSIBLE__
      addConstant name $ Defn name t0 (defaultDisplayForm name)
		       $ Record (size tel) Nothing
				(map getName fields) ftel s
				(Info.defAbstract i)
      return ()

{-| @checkRecordFields m q tel s ftel vs n fs@:
    @m@: name of the generated module
    @q@: name of the record
    @tel@: parameters
    @s@: sort of the record
    @ftel@: telescope of previous fields
    @vs@: values of previous fields (should have one free variable, which is
	  the record)
    @n@: total number of fields
    @fs@: the fields to be checked
-}
checkRecordFields :: ModuleName -> QName -> Telescope -> Sort ->
		     [(Name, Type)] -> [Term] -> Arity -> [A.Field] ->
		     TCM Telescope
checkRecordFields m q tel s ftel vs n [] = return EmptyTel
checkRecordFields m q tel s ftel vs n (f : fs) = do
  (x, a, v) <- checkField f
  let ftel' = ftel ++ [(x, a)]
  tel <- checkRecordFields m q tel s ftel' (v : vs) n fs
  return $ Arg NotHidden a `ExtendTel` Abs (show x) tel
  where
    checkField :: A.Field -> TCM (Name, Type, Term)
    checkField (A.ScopedDecl scope [f]) =
      setScope scope >> checkField f
    checkField (A.Axiom i x t) = do
      -- check the type (in the context of the telescope)
      -- the previous fields will be free in 
      reportSDoc "tc.rec.field" 5 $ sep
	[ text "checking field"
	, nest 2 $ vcat
	  [ text "top   =" <+> (prettyTCM =<< getContextTelescope)
	  , text "tel   =" <+> prettyTCM tel
	  , text "ftel1 =" <+> prettyList (map (prettyTCM . fst) ftel)
	  , text "ftel2 =" <+> prettyList (map (prettyTCM . snd) ftel)
	  , text "t     =" <+> prettyA t
	  , text "vs    =" <+> prettyList (map prettyTCM vs)
	  ]
	]
      let add (x, t) = addCtx x (Arg NotHidden t)
      t <- flip (foldr add) ftel $ isType_ t
      -- create the projection functions (instantiate the type with the values
      -- of the previous fields)

      {- what are the contexts?

	  tel, ftel    ⊢ t
	  tel, r       ⊢ vs
	  tel, r, ftel ⊢ raiseFrom (size ftel) 1 t
	  tel, r       ⊢ substs vs (raiseFrom (size ftel) 1 t)
      -}

      -- The type of the projection function should be
      -- {tel} -> (r : R Γ) -> t[vs/ftel]
      -- where Γ is the current context
      gamma <- getContextTelescope
      let hide (Arg _ x) = Arg Hidden x
	  htel	   = telFromList $ map hide $ telToList tel
	  rect	   = El s $ Def q $ reverse 
		      [ Arg h (Var i [])
		      | (i, Arg h _) <- zip [0..] $ reverse $ telToList gamma
		      ]
	  projt	   = substs (vs ++ map (flip Var []) [0..]) $ raiseFrom (size ftel) 1 t
	  finalt   = telePi htel
		   $ telePi (ExtendTel (Arg NotHidden rect) (Abs "r" EmptyTel))
		   $ projt
	  projname = qualify m $ qnameName x

      reportSDoc "tc.rec.field" 10 $ sep
	[ text "adding projection"
	, nest 2 $ prettyTCM projname <+> text ":" <+> prettyTCM finalt
	]

      -- The body should be
      --  P.xi {tel} (r _ .. x .. _) = x
      let hps	 = map (fmap $ VarP . fst) $ telToList htel
	  conp	 = Arg NotHidden
		 $ ConP q $ map (Arg NotHidden)
			    [ VarP "x" | _ <- [1..n] ]
	  nobind 0 = id
	  nobind n = NoBind . nobind (n - 1)
	  body	 = nobind (size htel)
		 $ nobind (size ftel)
		 $ Bind . Abs "x"
		 $ nobind (n - size ftel - 1)
		 $ Body $ Var 0 []
	  clause = Clause (hps ++ [conp]) body
      escapeContext (size tel) $
	addConstant projname (Defn projname finalt (defaultDisplayForm projname) $ Function [clause] ConcreteDef)

      -- The value of the projection is the projection function applied
      -- to the parameters and the record (these are free in the value)
      let projval = Def projname $
		    reverse [ Arg h (Var i [])
			    | (i, h) <- zip [0..size gamma] $ NotHidden : repeat Hidden
			    ]

      return (qnameName projname, t, projval)
    checkField _ = __IMPOSSIBLE__ -- record fields are always axioms

