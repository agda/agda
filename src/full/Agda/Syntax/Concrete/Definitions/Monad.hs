module Agda.Syntax.Concrete.Definitions.Monad where

import Control.Monad        ( unless )
import Control.Monad.Except ( MonadError(..), ExceptT, runExceptT )
import Control.Monad.State  ( MonadState(..), modify, State, runState )

import Data.Bifunctor (second)
import Data.Map (Map)
import qualified Data.Map as Map

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (TerminationCheck())
import Agda.Syntax.Concrete.Name
import Agda.Syntax.Concrete.Definitions.Types
import Agda.Syntax.Concrete.Definitions.Errors

import Agda.Utils.CallStack ( CallStack, HasCallStack, withCallerCallStack )
import Agda.Utils.Lens

import Agda.Utils.Impossible

-- | Nicifier monad.
--   Preserve the state when throwing an exception.

newtype Nice a = Nice { unNice :: ExceptT DeclarationException (State NiceEnv) a }
  deriving ( Functor, Applicative, Monad
           , MonadState NiceEnv, MonadError DeclarationException
           )

-- | Run a Nicifier computation, return result and warnings
--   (in chronological order).
runNice :: Nice a -> (Either DeclarationException a, NiceWarnings)
runNice m = second (reverse . niceWarn) $
  runExceptT (unNice m) `runState` initNiceEnv

-- | Nicifier state.

data NiceEnv = NiceEnv
  { _loneSigs :: LoneSigs
    -- ^ Lone type signatures that wait for their definition.
  , _termChk  :: TerminationCheck
    -- ^ Termination checking pragma waiting for a definition.
  , _posChk   :: PositivityCheck
    -- ^ Positivity checking pragma waiting for a definition.
  , _uniChk   :: UniverseCheck
    -- ^ Universe checking pragma waiting for a data/rec signature or definition.
  , _catchall :: Catchall
    -- ^ Catchall pragma waiting for a function clause.
  , _covChk  :: CoverageCheck
    -- ^ Coverage pragma waiting for a definition.
  , niceWarn :: NiceWarnings
    -- ^ Stack of warnings. Head is last warning.
  , _nameId  :: NameId
    -- ^ We distinguish different 'NoName's (anonymous definitions) by a unique 'NameId'.
  }

data LoneSig = LoneSig
  { loneSigRange :: Range
  , loneSigName  :: Name
      -- ^ If 'isNoName', this name can have a different 'NameId'
      --   than the key of 'LoneSigs' pointing to it.
  , loneSigKind  :: DataRecOrFun
  }

type LoneSigs     = Map Name LoneSig
     -- ^ We retain the 'Name' also in the codomain since
     --   'Name' as a key is up to @Eq Name@ which ignores the range.
     --   However, without range names are not unique in case the
     --   user gives a second definition of the same name.
     --   This causes then problems in 'replaceSigs' which might
     --   replace the wrong signature.
     --
     --   Another reason is that we want to distinguish different
     --   occurrences of 'NoName' in a mutual block (issue #4157).
     --   The 'NoName' in the codomain will have a unique 'NameId'.

type NiceWarnings = [DeclarationWarning]
     -- ^ Stack of warnings. Head is last warning.

-- | Initial nicifier state.

initNiceEnv :: NiceEnv
initNiceEnv = NiceEnv
  { _loneSigs = Map.empty
  , _termChk  = TerminationCheck
  , _posChk   = YesPositivityCheck
  , _uniChk   = YesUniverseCheck
  , _catchall = False
  , _covChk   = YesCoverageCheck
  , niceWarn  = []
  , _nameId   = NameId 1 noModuleNameHash
  }

lensNameId :: Lens' NameId NiceEnv
lensNameId f e = f (_nameId e) <&> \ i -> e { _nameId = i }

nextNameId :: Nice NameId
nextNameId = do
  i <- use lensNameId
  lensNameId %= succ
  return i

-- * Handling the lone signatures, stored to infer mutual blocks.

-- | Lens for field '_loneSigs'.

loneSigs :: Lens' LoneSigs NiceEnv
loneSigs f e = f (_loneSigs e) <&> \ s -> e { _loneSigs = s }

-- | Adding a lone signature to the state.
--   Return the name (which is made unique if 'isNoName').

addLoneSig :: Range -> Name -> DataRecOrFun -> Nice Name
addLoneSig r x k = do
  -- Andreas, 2020-05-19, issue #4157, make '_' unique.
  x' <- case x of
    Name{}     -> pure x
    NoName r _ -> NoName r <$> nextNameId
  loneSigs %== \ s -> do
    let (mr, s') = Map.insertLookupWithKey (\ _k new _old -> new) x (LoneSig r x' k) s
    case mr of
      Nothing -> return s'
      Just{}  -> declarationException $
        if not $ isNoName x then DuplicateDefinition x else DuplicateAnonDeclaration r
  return x'

-- | Remove a lone signature from the state.

removeLoneSig :: Name -> Nice ()
removeLoneSig x = loneSigs %= Map.delete x

-- | Search for forward type signature.

getSig :: Name -> Nice (Maybe DataRecOrFun)
getSig x = fmap loneSigKind . Map.lookup x <$> use loneSigs

-- | Check that no lone signatures are left in the state.

noLoneSigs :: Nice Bool
noLoneSigs = null <$> use loneSigs

-- | Ensure that all forward declarations have been given a definition.

forgetLoneSigs :: Nice ()
forgetLoneSigs = loneSigs .= Map.empty

checkLoneSigs :: LoneSigs -> Nice ()
checkLoneSigs xs = do
  forgetLoneSigs
  unless (Map.null xs) $ declarationWarning $ MissingDefinitions $
    map (\s -> (loneSigName s , loneSigRange s)) $ Map.elems xs

-- | Get names of lone function signatures, plus their unique names.

loneFuns :: LoneSigs -> [(Name,Name)]
loneFuns = map (second loneSigName) . filter (isFunName . loneSigKind . snd) . Map.toList

-- | Create a 'LoneSigs' map from an association list.

loneSigsFromLoneNames :: [(Range, Name, DataRecOrFun)] -> LoneSigs
loneSigsFromLoneNames = Map.fromListWith __IMPOSSIBLE__ . map (\(r,x,k) -> (x, LoneSig r x k))

-- | Lens for field '_termChk'.

terminationCheckPragma :: Lens' TerminationCheck NiceEnv
terminationCheckPragma f e = f (_termChk e) <&> \ s -> e { _termChk = s }

withTerminationCheckPragma :: TerminationCheck -> Nice a -> Nice a
withTerminationCheckPragma tc f = do
  tc_old <- use terminationCheckPragma
  terminationCheckPragma .= tc
  result <- f
  terminationCheckPragma .= tc_old
  return result

coverageCheckPragma :: Lens' CoverageCheck NiceEnv
coverageCheckPragma f e = f (_covChk e) <&> \ s -> e { _covChk = s }

withCoverageCheckPragma :: CoverageCheck -> Nice a -> Nice a
withCoverageCheckPragma tc f = do
  tc_old <- use coverageCheckPragma
  coverageCheckPragma .= tc
  result <- f
  coverageCheckPragma .= tc_old
  return result

-- | Lens for field '_posChk'.

positivityCheckPragma :: Lens' PositivityCheck NiceEnv
positivityCheckPragma f e = f (_posChk e) <&> \ s -> e { _posChk = s }

withPositivityCheckPragma :: PositivityCheck -> Nice a -> Nice a
withPositivityCheckPragma pc f = do
  pc_old <- use positivityCheckPragma
  positivityCheckPragma .= pc
  result <- f
  positivityCheckPragma .= pc_old
  return result

-- | Lens for field '_uniChk'.

universeCheckPragma :: Lens' UniverseCheck NiceEnv
universeCheckPragma f e = f (_uniChk e) <&> \ s -> e { _uniChk = s }

withUniverseCheckPragma :: UniverseCheck -> Nice a -> Nice a
withUniverseCheckPragma uc f = do
  uc_old <- use universeCheckPragma
  universeCheckPragma .= uc
  result <- f
  universeCheckPragma .= uc_old
  return result

-- | Get universe check pragma from a data/rec signature.
--   Defaults to 'YesUniverseCheck'.

getUniverseCheckFromSig :: Name -> Nice UniverseCheck
getUniverseCheckFromSig x = maybe YesUniverseCheck universeCheck <$> getSig x

-- | Lens for field '_catchall'.

catchallPragma :: Lens' Catchall NiceEnv
catchallPragma f e = f (_catchall e) <&> \ s -> e { _catchall = s }

-- | Get current catchall pragma, and reset it for the next clause.

popCatchallPragma :: Nice Catchall
popCatchallPragma = do
  ca <- use catchallPragma
  catchallPragma .= False
  return ca

withCatchallPragma :: Catchall -> Nice a -> Nice a
withCatchallPragma ca f = do
  ca_old <- use catchallPragma
  catchallPragma .= ca
  result <- f
  catchallPragma .= ca_old
  return result

-- | Add a new warning.
niceWarning :: DeclarationWarning -> Nice ()
niceWarning w = modify $ \ st -> st { niceWarn = w : niceWarn st }

declarationException :: HasCallStack => DeclarationException' -> Nice a
declarationException e = withCallerCallStack $ throwError . flip DeclarationException e

declarationWarning' :: DeclarationWarning' -> CallStack -> Nice ()
declarationWarning' w loc = niceWarning $ DeclarationWarning loc w

declarationWarning :: HasCallStack => DeclarationWarning' -> Nice ()
declarationWarning = withCallerCallStack . declarationWarning'
