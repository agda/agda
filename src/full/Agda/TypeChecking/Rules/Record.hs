{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Rules.Record where

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Reader

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position
import qualified Agda.Syntax.Info as Info

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Polarity

import Agda.TypeChecking.Rules.Data ( bindParameters, fitsIn )
import Agda.TypeChecking.Rules.Term ( isType_ )
import {-# SOURCE #-} Agda.TypeChecking.Rules.Decl (checkDecl)

import Agda.Utils.Size
import Agda.Utils.Permutation

#include "../../undefined.h"
import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Records
---------------------------------------------------------------------------

checkRecDef :: Info.DefInfo -> QName -> [A.LamBinding] -> A.Expr -> [A.Constructor] -> TCM ()
checkRecDef i name ps contel fields =
  noMutualBlock $ -- records can't be recursive anyway
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
          extWithR ret   = underAbstraction (Arg NotHidden rect) (Abs "r" ()) $ \_ -> ret
          ext (Arg h (x, t)) = addCtx x (Arg h t)

      let getName (A.Field _ x _)      = [x]
	  getName (A.ScopedDecl _ [f]) = getName f
	  getName _		       = []

      ctx <- (reverse . map hide . take (size tel)) <$> getContext

      -- We have to rebind the parameters to make them hidden
      -- Check the field telescope
      contype <- killRange <$> (instantiateFull =<< isType_ contel)
      let TelV ftel _ = telView contype

      escapeContext (size tel) $ flip (foldr ext) ctx $ extWithR $ do
	reportSDoc "tc.rec.def" 10 $ sep
	  [ text "record section:"
	  , nest 2 $ sep
            [ prettyTCM m <+> (prettyTCM =<< getContextTelescope)
            , fsep $ punctuate comma $ map (text . show . getName) fields
            ]
	  ]
        reportSDoc "tc.rec.def" 15 $ nest 2 $ vcat
          [ text "field tel =" <+> prettyTCM ftel
          ]
	addSection m (size tel')

        -- Check the types of the fields
        -- ftel <- checkRecordFields m name tel s [] (size fields) fields
        withCurrentModule m $ checkRecordProjections m name tel' (raise 1 ftel) s fields

      -- Check that the fields fit inside the sort
      telePi ftel t0 `fitsIn` s

      addConstant name $ Defn name t0 (defaultDisplayForm name) 0
		       $ Record { recPars           = size tel
                                , recClause         = Nothing
				, recFields         = concatMap getName fields
                                , recTel            = ftel
                                , recSort           = s
				, recAbstr          = Info.defAbstract i
                                , recPolarity       = []
                                , recArgOccurrences = []
                                }
      computePolarity name

      return ()

{-| @checkRecordProjections q tel ftel s vs n fs@:
    @m@: name of the generated module
    @q@: name of the record
    @tel@: parameters
    @s@: sort of the record
    @ftel@: telescope of fields
    @vs@: values of previous fields (should have one free variable, which is
	  the record)
    @fs@: the fields to be checked
-}
checkRecordProjections ::
  ModuleName -> QName -> Telescope -> Telescope -> Sort ->
  [A.Declaration] -> TCM ()
checkRecordProjections m q tel ftel s fs = checkProjs EmptyTel ftel fs
  where
    checkProjs :: Telescope -> Telescope -> [A.Declaration] -> TCM ()
    checkProjs _ _ [] = return ()
    checkProjs ftel1 ftel2 (A.ScopedDecl scope fs' : fs) =
      setScope scope >> checkProjs ftel1 ftel2 (fs' ++ fs)
    checkProjs ftel1 (ExtendTel (Arg _ _) ftel2) (A.Field info x t : fs) = do
      -- check the type (in the context of the telescope)
      -- the previous fields will be free in 
      reportSDoc "tc.rec.proj" 5 $ sep
	[ text "checking projection"
	, nest 2 $ vcat
	  [ text "top   =" <+> (prettyTCM =<< getContextTelescope)
	  , text "ftel1 =" <+> prettyTCM ftel1
	  , text "ftel2 =" <+> addCtxTel ftel1 (underAbstraction_ ftel2 prettyTCM)
	  , text "t     =" <+> prettyTCM t
	  ]
	]
      let add (x, t) = addCtx x (Arg NotHidden t)
          n          = size ftel

      t <- isType_ t

      -- create the projection functions (instantiate the type with the values
      -- of the previous fields)

      {- what are the contexts?

	  Γ, tel            ⊢ t
	  Γ, tel, r         ⊢ vs
	  Γ, tel, r, ftel₁  ⊢ raiseFrom (size ftel₁) 1 t
      -}

      -- The type of the projection function should be
      --  {tel} -> (r : R Δ) -> t
      -- where Δ = Γ, tel is the current context
      delta <- getContextTelescope
      let finalt   = telePi tel t
	  projname = qualify m $ qnameName x

      reportSDoc "tc.rec.proj" 10 $ sep
	[ text "adding projection"
	, nest 2 $ prettyTCM projname <+> text ":" <+> prettyTCM finalt
	]

      -- The body should be
      --  P.xi {tel} (r _ .. x .. _) = x
      let ptel   = telFromList $ take (size tel - 1) $ telToList tel
          hps	 = map (fmap $ VarP . fst) $ telToList ptel
	  conp	 = Arg NotHidden
		 $ ConP q $ map (Arg NotHidden)
			    [ VarP "x" | _ <- [1..n] ]
	  nobind 0 = id
	  nobind n = NoBind . nobind (n - 1)
	  body	 = nobind (size tel - 1)
		 $ nobind (size ftel1)
		 $ Bind . Abs "x"
		 $ nobind (size ftel2)
		 $ Body $ Var 0 []
          cltel  = ptel `abstract` ftel
	  clause = Clause { clauseRange = getRange info
                          , clauseTel   = cltel
                          , clausePerm  = idP $ size ptel + size ftel
                          , clausePats  = hps ++ [conp]
                          , clauseBody  = body
                          }
      escapeContext (size tel) $ do
	addConstant projname $ Defn projname finalt (defaultDisplayForm projname) 0
          $ Function { funClauses        = [clause]
                     , funInv            = NotInjective
                     , funAbstr          = ConcreteDef
                     , funPolarity       = []
                     , funArgOccurrences = map (const Unused) hps ++ [Negative]
                     }
        computePolarity projname

      checkProjs (abstract ftel1 $ ExtendTel (Arg NotHidden t)
                                 $ Abs (show $ qnameName projname) EmptyTel
                 ) (absBody ftel2) fs
    checkProjs ftel1 ftel2 (d : fs) = do
      checkDecl d
      checkProjs ftel1 ftel2 fs

