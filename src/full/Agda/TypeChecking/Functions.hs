
module Agda.TypeChecking.Functions
  ( etaExpandClause
  , getDef
  ) where

import Control.Arrow ( first )

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Level
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Impossible
import Agda.Utils.Functor ( ($>) )
import Agda.Utils.Pretty ( prettyShow )
import Agda.Utils.Monad
import Agda.Utils.Size


-- | Expand a clause to the maximal arity, by inserting variable
--   patterns and applying the body to variables.

--  Fixes issue #2376.
--  Replaces 'introHiddenLambdas'.
--  See, e.g., test/Succeed/SizedTypesExtendedLambda.agda.

--  This is used instead of special treatment of lambdas
--  (which was unsound: Issue #121)

etaExpandClause :: MonadTCM tcm => Clause -> tcm Clause
etaExpandClause clause = liftTCM $ do
  case clause of
    Clause _  _  ctel ps _           Nothing  _ _ _ -> return clause
    Clause _  _  ctel ps Nothing     (Just t) _ _ _ -> return clause
    Clause rl rf ctel ps (Just body) (Just t) catchall unreachable ell -> do

      -- Get the telescope to expand the clause with.
      TelV tel0 t' <- telView $ unArg t

      -- If the rhs has lambdas, harvest the names of the bound variables.
      let xs   = peekLambdas body
      let ltel = useNames xs $ telToList tel0
      let tel  = telFromList ltel
      let n    = size tel
      unless (n == size tel0) __IMPOSSIBLE__  -- useNames should not drop anything
      -- Join with lhs telescope, extend patterns and apply body.
      -- NB: no need to raise ctel!
      let ctel' = telFromList $ telToList ctel ++ ltel
          ps'   = raise n ps ++ teleNamedArgs tel
          body' = raise n body `apply` teleArgs tel
      reportSDoc "term.clause.expand" 30 $ inTopContext $ vcat
        [ "etaExpandClause"
        , "  body    = " <+> (addContext ctel' $ prettyTCM body)
        , "  xs      = " <+> text (prettyShow xs)
        , "  new tel = " <+> prettyTCM ctel'
        ]
      return $ Clause rl rf ctel' ps' (Just body') (Just (t $> t')) catchall unreachable ell
  where
    -- Get all initial lambdas of the body.
    peekLambdas :: Term -> [Arg ArgName]
    peekLambdas v =
      case v of
        Lam info b -> Arg info (absName b) : peekLambdas (unAbs b)
        _ -> []

    -- Use the names of the first argument, and set the Origin all other
    -- parts of the telescope to Inserted.
    -- The first list of arguments is a subset of the telescope.
    -- Thus, if compared pointwise, if the hiding does not match,
    -- it means we skipped an element of the telescope.
    useNames :: [Arg ArgName] -> ListTel -> ListTel
    useNames []     tel       = map (setOrigin Inserted) tel
    -- Andrea: we can have more Lam's than Pi's, because they might be for Path
    -- Andreas, 2017-03-24: the following case is not IMPOSSIBLE when positivity checking comes before termination checking, see examples/tactics/ac/AC.agda
    useNames (_:_)  []        = []
    useNames (x:xs) (dom:tel)
      | sameHiding x dom =
          -- set the ArgName of the dom
          fmap (first $ const $ unArg x) dom : useNames xs tel
      | otherwise =
          setOrigin Inserted dom : useNames (x:xs) tel

-- | Get the name of defined symbol of the head normal form of a term.
--   Returns 'Nothing' if no such head exists.

getDef :: Term -> TCM (Maybe QName)
getDef t = reduce t >>= \case
  Def d _    -> return $ Just d
  Lam _ v    -> underAbstraction_ v getDef
  Level v    -> getDef =<< reallyUnLevelView v
  DontCare v -> getDef v
  _          -> return Nothing
