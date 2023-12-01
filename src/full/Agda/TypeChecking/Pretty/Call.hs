{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Pretty.Call where

import Prelude hiding ( null )

import Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Views
import Agda.Syntax.Common
import Agda.Syntax.Fixity
import qualified Agda.Syntax.Concrete.Definitions as D
import qualified Agda.Syntax.Info as A
import Agda.Syntax.Position
import Agda.Syntax.Internal
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Translation.AbstractToConcrete

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Pretty

import Agda.Utils.Function
import Agda.Utils.Null
import qualified Agda.Syntax.Common.Pretty as P

import Agda.Utils.Impossible

import Agda.Version (docsUrl)

sayWhere :: MonadPretty m => HasRange a => a -> m Doc -> m Doc
sayWhere x d = applyUnless (null r) (prettyTCM r $$) d
  where r = getRange x

sayWhen :: MonadPretty m => Range -> Maybe (Closure Call) -> m Doc -> m Doc
sayWhen r Nothing   m = sayWhere r m
sayWhen r (Just cl) m = sayWhere r (m $$ prettyTCM cl)

instance PrettyTCM CallInfo where
  prettyTCM (CallInfo callInfoTarget callInfoCall) = do
    let call = prettyTCM callInfoCall
        r    = getRange callInfoTarget
    if null $ P.pretty r
      then call
      else call $$ nest 2 ("(at" <+> prettyTCM r) <> ")"
  {-# SPECIALIZE prettyTCM :: CallInfo -> TCM Doc #-}

instance PrettyTCM Call where
  prettyTCM = withContextPrecedence TopCtx . \case

    CheckClause t cl -> do

      verboseS  "error.checkclause" 40 $ do
        reportSLn "error.checkclause" 60 $ "prettyTCM CheckClause: cl = " ++ show (deepUnscope cl)
        clc <- abstractToConcrete_ cl
        reportSLn "error.checkclause" 40 $ "cl (Concrete) = " ++ show clc

      fsep $
        pwords "when checking that the clause"
        ++ [prettyA cl] ++ pwords "has type" ++ [prettyTCM t]

    CheckLHS lhs -> vcat $
      [ fsep $ pwords "when checking the clause left hand side"
      , prettyA $ lhs { A.spLhsInfo = (A.spLhsInfo lhs) { A.lhsEllipsis = NoEllipsis } }
      ]

    CheckPattern p tel t -> addContext tel $ fsep $
      pwords "when checking that the pattern"
      ++ [prettyA p] ++ pwords "has type" ++ [prettyTCM t]

    CheckPatternLinearityType x -> fsep $
      pwords "when checking that all occurrences of pattern variable"
      ++ [pretty x] ++ pwords "have the same type"

    CheckPatternLinearityValue x -> fsep $
      pwords "when checking that all occurrences of pattern variable"
      ++ [pretty x] ++ pwords "have the same value"

    CheckLetBinding b -> fsep $
      pwords "when checking the let binding" ++ [prettyA b]

    InferExpr e -> fsep $ pwords "when inferring the type of" ++ [prettyA e]

    CheckExprCall cmp e t -> fsep $
      pwords "when checking that the expression"
      ++ [prettyA e] ++ pwords "has type" ++ [prettyTCM t]

    IsTypeCall cmp e s -> fsep $
      pwords "when checking that the expression"
      ++ [prettyA e] ++ pwords "is a type of sort" ++ [prettyTCM s]

    IsType_ e -> fsep $
      pwords "when checking that the expression"
      ++ [prettyA e] ++ pwords "is a type"

    CheckProjection _ x t -> fsep $
      pwords "when checking the projection" ++
      [ sep [ prettyTCM x <+> ":"
            , nest 2 $ prettyTCM t ] ]

    CheckArguments r es t0 t1 -> do
      TelV tel cod <- telView t0
      let
        prefix =
          pwords "when checking that" ++
          map hPretty es ++
          pwords (P.singPlural es "is a valid argument" "are valid arguments")
      case unEl cod of
        Dummy{} -> fsep $
          prefix ++
          pwords "to a function accepting arguments of type" ++
          [prettyTCM tel]
        _ -> fsep $
          prefix ++
          pwords "to a function of type" ++
          [prettyTCM t0]

    CheckMetaSolution r m a v -> fsep $
      pwords "when checking that the solution" ++ [prettyTCM v] ++
      pwords "of metavariable" ++ [prettyTCM m] ++
      pwords "has the expected type" ++ [prettyTCM a]

    CheckTargetType r infTy expTy -> sep
      [ "when checking that the inferred type of an application"
      , nest 2 $ prettyTCM infTy
      , "matches the expected type"
      , nest 2 $ prettyTCM expTy ]

    CheckRecDef _ x ps cs ->
      fsep $ pwords "when checking the definition of" ++ [prettyTCM x]

    CheckDataDef _ x ps cs ->
      fsep $ pwords "when checking the definition of" ++ [prettyTCM x]

    CheckConstructor d _ _ (A.Axiom _ _ _ _ c _) -> fsep $
      pwords "when checking the constructor" ++ [prettyTCM c] ++
      pwords "in the declaration of" ++ [prettyTCM d]

    CheckConstructor{} -> __IMPOSSIBLE__

    CheckConArgFitsIn c f t s -> do
      woK <- withoutKOption
      let
        hint = fsep (pwords "Note: this argument is forced by the indices of" ++ [prettyTCM c <> comma] ++ pwords "so this definition would be allowed under --large-indices.")
        -- Only add hint about large-indices when --with-K
        addh d
          | f && not woK = d $$ empty $$ hint
          | otherwise    = d

      addh $ fsep $
        pwords "when checking that the type" ++ [prettyTCM t] ++
        pwords "of an argument to the constructor" ++ [prettyTCM c] ++
        pwords "fits in the sort" ++ [prettyTCM s] ++
        pwords "of the datatype."

    CheckFunDefCall _ f _ _ ->
      fsep $ pwords "when checking the definition of" ++ [prettyTCM f]

    CheckPragma _ p ->
      fsep $ pwords "when checking the pragma"
             ++ [prettyA $ RangeAndPragma noRange p]

    CheckPrimitive _ x e -> fsep $
      pwords "when checking that the type of the primitive function" ++
      [prettyTCM x] ++ pwords "is" ++ [prettyA e]

    CheckModuleParameters m _tel -> fsep $
      pwords "when checking the parameters of module" ++ [prettyA m]

    CheckWithFunctionType a -> fsep $
      pwords "when checking that the type" ++
      [prettyTCM a] ++ pwords "of the generated with function is well-formed" ++
      [parens $ text $ docsUrl "language/with-abstraction.html#ill-typed-with-abstractions"]

    CheckDotPattern e v -> fsep $
      pwords "when checking that the given dot pattern" ++ [prettyA e] ++
      pwords "matches the inferred value" ++ [prettyTCM v]

    CheckNamedWhere m -> fsep $
      pwords "when checking the named where block" ++ [prettyA m]

    InferVar x ->
      fsep $ pwords "when inferring the type of" ++ [prettyTCM x]

    InferDef x ->
      fsep $ pwords "when inferring the type of" ++ [prettyTCM x]

    CheckIsEmpty r t ->
      fsep $ pwords "when checking that" ++ [prettyTCM t] ++
             pwords "has no constructors"

    CheckConfluence r1 r2 ->
      fsep $ pwords "when checking confluence of the rewrite rule" ++
             [prettyTCM r1] ++ pwords "with" ++
             if r1 == r2 then pwords "itself" else [prettyTCM r2]

    ScopeCheckExpr e -> fsep $ pwords "when scope checking" ++ [pretty e]

    ScopeCheckDeclaration d ->
      fwords ("when scope checking the declaration" ++ suffix) $$
      nest 2 (vcat $ map pretty ds)
      where
      ds     = D.notSoNiceDeclarations d
      suffix = case ds of
        [_] -> ""
        _   -> "s"

    ScopeCheckLHS x p ->
      fsep $ pwords "when scope checking the left-hand side" ++ [pretty p] ++
             pwords "in the definition of" ++ [pretty x]

    NoHighlighting -> empty

    SetRange r -> fsep (pwords "when doing something at") <+> prettyTCM r

    CheckSectionApplication _ erased m1 modapp -> fsep $
      pwords "when checking the module application" ++
      [prettyA $ A.Apply info erased m1 modapp initCopyInfo empty]
      where
      info = A.ModuleInfo noRange noRange Nothing Nothing Nothing

    ModuleContents -> fsep $ pwords "when retrieving the contents of a module"

    CheckIApplyConfluence _ qn fn l r t -> do
      vcat
        [ fsep (pwords "when checking that a clause of" ++ [prettyTCM qn] ++ pwords "has the correct boundary.")
        , ""
        , "Specifically, the terms"
        , nest 2 (prettyTCM l)
        , "and"
        , nest 2 (prettyTCM r)
        , fsep (pwords "must be equal, since" ++ [prettyTCM fn] ++ pwords "could reduce to either.")
        ]

    where
    hPretty :: MonadPretty m => Arg (Named_ Expr) -> m Doc
    hPretty a = do
      withContextPrecedence (ArgumentCtx PreferParen) $
        pretty =<< abstractToConcreteHiding a a
  {-# SPECIALIZE prettyTCM :: Call -> TCM Doc #-}
