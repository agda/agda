module Agda.Interaction.Widget.Errors where

import Prelude hiding (null)

import Agda.Interaction.Widget

import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Reduce

import Agda.TypeChecking.Pretty.Call ()
import Agda.TypeChecking.Errors ()
import Agda.TypeChecking.Pretty

import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Position
import Agda.Utils.Monad
import Agda.Utils.Null

import qualified Agda.Utils.SmallSet as SmallSet
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Function

import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import Data.IORef
import Data.Kind

instance ToWidget Call where
  toWidget :: forall m. MonadWidget m => Call -> m (Dynamic m Doc)
  toWidget = \case
    CheckIApplyConfluence _ qn fn l r t -> do
      let
        t :: I.Term -> Dynamic m I.Term
        t x = putAllowedReductions SmallSet.empty $ case x of
          I.Def f xs -> I.Def f <$> normalise xs
          _ -> pure fn

      l <- cycleBetween'
        [ prettyTCM fn
        , prettyTCM =<< t fn
        , prettyTCM l
        , prettyTCM =<< reduce l
        ]

      r <- cycleBetween'
        [ prettyTCM r
        , prettyTCM =<< t r
        , prettyTCM =<< reduce r
        ]

      thefn <- eagerly $ hiFunction (prettyTCM qn)
      (shown, trigger) <- newDynamic False not

      let tooltip = ifM shown (pure "mouse-1: Hide the boundary")
                              (pure "mouse-1: Show the boundary")
      pure $ vcat
        [ fsep (pwords "when checking that a clause of" ++ [thefn] ++ pwords "has the correct boundary.")
        , ifM shown
            (vcat [ empty, "The terms"
                  , nest 2 l
                  , "and"
                  , nest 2 r
                  , fsep (pwords "must be equal.") ])
            empty
        , parens $ hiTooltip tooltip $ hiInteraction $
          triggerOnClick trigger $
          ifM shown "Show less" "Show more"
        ]

    x -> pure $ prettyTCM x

sayWhere' :: MonadWidget m => HasRange a => a -> m (Dynamic m Doc) -> m (Dynamic m Doc)
sayWhere' x d = do
  d <- d
  pure $ applyUnless (null r) (prettyTCM r $$) d
  where r = getRange x

sayWhen' :: MonadWidget m
         => Range -> Maybe (Closure Call) -> m (Dynamic m Doc) -> m (Dynamic m Doc)
sayWhen' r Nothing   m = sayWhere' r m
sayWhen' r (Just cl) m = sayWhere' r (($$) <$> m <*> toWidget cl)

panic' :: MonadWidget m => String -> m (Dynamic m Doc)
panic' s = pure $ fwords $ "Panic: " ++ s

instance ToWidget TypeError where
  toWidget = pure . prettyTCM

instance ToWidget TCErr where
  toWidget err = case err of
    -- Gallais, 2016-05-14
    -- Given where `NonFatalErrors` are created, we know for a
    -- fact that ̀ws` is non-empty.
    TypeError loc _ Closure{ clValue = NonFatalErrors ws } -> pure $ do
      reportSLn "error" 2 $ "Error raised at " ++ P.prettyShow loc
      foldr1 ($$) $ fmap prettyTCM ws

    -- Andreas, 2014-03-23
    -- This use of withTCState seems ok since we do not collect
    -- Benchmark info during printing errors.
    TypeError loc s e ->
      -- Must re-enter saved state to generate the widget:
      withTCState (const s) $ do
        reportSLn "error" 2 $ "Error raised at " ++ P.prettyShow loc
        r <- sayWhen' (envRange $ clEnv e) (envCall $ clEnv e) $ toWidget e
        pure $
          -- Must re-enter saved state when rendering, too:
          withTCState (const s) r
      -- This state shuffling ensures both generating the structure and
      -- rendering the generated structure will happen in the same state

    Exception r s     -> sayWhere' r $ pure $ pure s
    IOException _ r e -> sayWhere' r $ pure $ fwords $ show e
    PatternErr{}      -> sayWhere' err $ panic' "uncaught pattern violation"
