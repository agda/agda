module MetaVars where
type MetaVar = Int

preMetaVar :: MetaVar
preMetaVar = -1

type ParseInfo = Bool

type Visibility = Maybe Bool
-- Nothing means that the metavariable isn't visible
-- Just aut menas that the metavariable is visible and the
-- bool aut indicates if it should be automatically solved or not, i.e. an _ metavariable.

isAutomatic Nothing = True  -- a hidden metavariable should be automatically solved
isAutomatic (Just aut) = aut

mkAutomatic Nothing = Nothing
mkAutomatic (Just _) = Just True

isVisible Nothing = False
isVisible _ = True

isVisAut Nothing = False
isVisAut (Just aut) = aut
