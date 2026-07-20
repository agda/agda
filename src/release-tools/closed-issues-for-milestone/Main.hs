{-# LANGUAGE BlockArguments            #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RecordWildCards           #-}

module Main ( main ) where

import Control.Monad
import Data.Bifunctor  ( bimap )
import Data.Char       ( isSpace )
import Data.Foldable
import Data.Functor
import Data.List       ( partition )
import Data.Maybe
import Data.Text ( Text )
import qualified Data.Text as Text
import qualified Data.ByteString.Char8 as BS
import qualified Data.ByteString.Lazy as LBS

import Data.YAML
  ( FromYAML( parseYAML )
  , decode1Strict
  , prettyPosWithSource
  , withMap
  , (.:)
  )

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.Vector as V

import System.Console.GetOpt
  ( ArgOrder( Permute )
  , ArgDescr( NoArg, ReqArg )
  , OptDescr( Option )
  , getOpt
  , usageInfo
  )
import System.Environment ( getArgs, getEnv, getProgName )
import System.Exit        ( die )
import System.IO          ( hPutStrLn, stderr )
import System.IO.Error    ( tryIOError )

import GitHub.Auth
  ( Auth( OAuth )
  )
import GitHub.Data.Definitions
  ( IssueLabel ( labelName )
  , unIssueNumber
  )
import GitHub.Data.Issues
  ( Issue( Issue
         , issueLabels
         , issueMilestone
         , issueNumber
         , issuePullRequest
         , issueStateReason
         , issueTitle
         )
  )
import GitHub.Data.Id
  ( Id
  )
import GitHub.Data.Name
  ( Name( N )
  , untagName
  )
import GitHub.Data.Milestone
  ( Milestone( milestoneNumber, milestoneTitle )
  )
import GitHub.Data.Options
  ( optionsMilestone
  , stateClosed
  , IssueStateReason( StateReasonNotPlanned )
  )
import GitHub.Data.Request
  ( FetchCount(FetchAll)
  )
import GitHub.Endpoints.Issues.Milestones
  ( milestonesR
  )
import GitHub.Endpoints.Issues
  ( issuesForRepoR
  )
import GitHub.Endpoints.PullRequests
  ( isPullRequestMergedR
  )
import GitHub.Request
  ( github
  )

envGHToken :: String
envGHToken = "GITHUB_TOKEN"

owner, repo :: Text
owner = "agda"
repo  = "agda"

theRepo :: String
theRepo = Text.unpack owner ++ "/" ++ Text.unpack repo

defaultConfigFile :: FilePath
defaultConfigFile = ".github/release.yml"

data Flag
  = Config FilePath
  | Help
  deriving (Eq)

commandLineOptions :: [OptDescr Flag]
commandLineOptions =
  [ Option [] ["config"] (ReqArg Config "FILE") $
      "Load release configuration from FILE (default: " ++ defaultConfigFile ++ ")"
  , Option ['h'] ["help"] (NoArg Help) "Show this help text"
  ]

main :: IO ()
main = do
  progName <- getProgName
  (flags, args, errors) <- getOpt Permute commandLineOptions <$> getArgs
  if Help `elem` flags then
    putStrLn $ usageText progName
  else case (errors, [ file | Config file <- flags ], args) of
    ([], [],     [milestone]) -> runWithConfig defaultConfigFile $ Text.pack milestone
    ([], [file], [milestone]) -> runWithConfig file              $ Text.pack milestone
    ([], _ : _ : _, _)       -> dieWithUsage progName "Option --config can only be specified once."
    ([], _, _)                -> dieWithUsage progName "Expected exactly one milestone."
    _                         -> dieWithUsage progName $ concat errors

usageText :: String -> String
usageText progName = usageInfo header commandLineOptions
  where
  header = unlines
    [ "Usage: " ++ progName ++ " [--config FILE] <milestone>"
    , ""
    , "Retrieves closed issues for the given milestone from github repository"
    , theRepo ++ " and prints them as markdown to stdout."
    , ""
    , "Expects an access token in environment variable GITHUB_TOKEN."
    ]

dieWithUsage :: String -> String -> IO a
dieWithUsage progName message = die $ message ++ "\n\n" ++ usageText progName

debugPrint :: String -> IO ()
debugPrint = hPutStrLn stderr

type Label = Text

newtype ReleaseConfig = ReleaseConfig
  { labelsNotInChangelog :: [Label]
  }

instance FromYAML ReleaseConfig where
  parseYAML = withMap "release configuration" $ \ config -> do
    changelog <- config .: "changelog"
    withMap "changelog" (\ changelogConfig -> do
      exclude <- changelogConfig .: "exclude"
      withMap "exclude" (\ excludeConfig ->
        ReleaseConfig <$> excludeConfig .: "labels"
        ) exclude
      ) changelog

loadReleaseConfig :: FilePath -> IO ReleaseConfig
loadReleaseConfig file = do
  contents <- either (die . readError) pure =<< tryIOError (BS.readFile file)
  case decode1Strict contents of
    Left (position, message) -> die $
      file ++ ":" ++ prettyPosWithSource position (LBS.fromStrict contents) " error" ++ message
    Right config -> pure config
  where
  readError err = "Could not read release configuration " ++ file ++ ": " ++ show err

runWithConfig :: FilePath -> Text -> IO ()
runWithConfig configFile milestone = do
  ReleaseConfig{ labelsNotInChangelog } <- loadReleaseConfig configFile
  debugPrint $ "Excluded labels loaded from " ++ configFile ++ ":"
  forM_ labelsNotInChangelog $ \ label ->
    debugPrint $ "- " ++ Text.unpack label
  debugPrint ""
  run (Set.fromList labelsNotInChangelog) milestone

issueLabelsNames :: Issue -> [Label]
issueLabelsNames i = map (untagName . labelName) $ V.toList $ issueLabels i

-- | Classification of issues.
--
-- We filter issues by the following criteria:
-- 1. Correct milestone or wrong milestone (the latter should be impossible).
-- 2. Issue or PR.
-- 3. Happened (regular close or merge) or didn't happen (close as not planned or closed without merge).
-- 4. Should be listed or not (in the latter case, give the labels that indicate it should not be listed).

data Class = Class
  { correctMilestone :: Bool       -- ^ False if milestone is not the one we requested.
  , isIssue          :: Bool       -- ^ False if PR.
  , happened         :: Bool       -- ^ False if closed as not planned or closed without merge.
  , goodLabels       :: Set Label  -- ^ Labels that do not affect inclusion in changelog.
  , badLabels        :: Set Label  -- ^ Labels that prevent inclusion in changelog
  }

-- | Issue enriched with its classification.
--
data ClassifiedIssue = ClassifiedIssue
  { theIssue   :: Issue
  , issueClass :: Class
  }

-- | This classifies issue numbers,
--   but the field 'happened' is only set correctly for issues, not for milestones.
--
classifyIssue :: Set Label -> Id Milestone -> Issue -> Class
classifyIssue labelsNotInChangelog mileStoneId i = Class{..}
  where
  correctMilestone        = maybe False ((mileStoneId ==) . milestoneNumber) $ issueMilestone i
  isIssue                 = isNothing $ issuePullRequest i
  happened                = maybe True (StateReasonNotPlanned /=) $ issueStateReason i
  (badLabels, goodLabels) = bimap Set.fromList Set.fromList $
     partition (`Set.member` labelsNotInChangelog) $ issueLabelsNames i

-- | Delete trailing whitespace from issue
sanitizeIssue :: Issue -> Issue
sanitizeIssue i = i{ issueTitle = trim $ issueTitle i }
  where
    trim = Text.dropWhileEnd isSpace

-- | Format issue in markdown for printing.
--
printIssue :: Issue -> String
printIssue Issue{ issueNumber, issueTitle, issuePullRequest } = do
  let n = show $ unIssueNumber issueNumber
  let issuePR = if isNothing issuePullRequest then "Issue" else "PR"
  concat
    [ "[", issuePR, " #", n, "]"
    , "(https://github.com/", theRepo, "/issues/", n, ")"
    , ": ", Text.unpack issueTitle
    ]

debugPrintIssues :: [ClassifiedIssue] -> String -> IO ()
debugPrintIssues is title =
  unless (null is) do
    debugPrint title
    forM_ is $ \ (ClassifiedIssue i _c) -> debugPrint $ "- " ++ printIssue i
    debugPrint ""


-- | Retrieve closed issues for the given milestone and print as csv to stdout.
run :: Set Label -> Text -> IO ()
run labelsNotInChangelog mileStoneTitle = do

  -- Get authentication token from environment.
  auth <- OAuth . BS.pack <$> getEnv envGHToken

  -- Log in to repo.

  debugPrint $ "Getting milestone " ++ Text.unpack mileStoneTitle

  -- Resolve milestone into milestone id.
  mileStoneVector <- crashOr $ github auth $ milestonesR (N owner) (N repo) FetchAll
  mileStoneId <- case filter ((mileStoneTitle ==) . milestoneTitle) $ toList mileStoneVector of
    []  -> die $ "Milestone " ++ Text.unpack mileStoneTitle ++ " not found in github repo " ++ theRepo
    [m] -> return $ milestoneNumber m
    _   -> die $ "Milestone " ++ Text.unpack mileStoneTitle ++ " ambiguous in github repo " ++ theRepo

  -- Debug.
  debugPrint $ "Getting issues for milestone number " ++ show mileStoneId

  let issueFilter = optionsMilestone mileStoneId <> stateClosed
  -- Get list of issues. GitHub's REST API v3 considers every pull
  -- request an issue. For this reason we get a list of both issues
  -- and pull requests when using the function 'issuesForRepo''.
  issueVector <- crashOr $ github auth $ issuesForRepoR (N owner) (N repo) issueFilter FetchAll

  -- Classify issues and remove trailing whitespace from the issue title.
  let issues0 :: [ClassifiedIssue]
      issues0 = reverse (toList issueVector) <&> \ i ->
        ClassifiedIssue (sanitizeIssue i) (classifyIssue labelsNotInChangelog mileStoneId i)

  -- We progressively filter out issue numbers not included in changelog.

  -- Filter out issues/PRs with wrong milestone:
  let (issues1, wrongMilestone) = partition (correctMilestone . issueClass) issues0
  debugPrintIssues wrongMilestone "Issues/PR with wrong milestone:"

  -- Filter out issues that were "Closed as not planned"
  let (issues2, didNotHappen) = partition (happened . issueClass) issues1
  debugPrintIssues didNotHappen "Issues closed as not planned"

  -- Find out which PRs were closed without merging
  issues3 <- forM issues2 $ \ ic@(ClassifiedIssue i c) -> do
    if isIssue c then pure ic else do
      merged <- crashOr $ github auth $ isPullRequestMergedR (N owner) (N repo) (issueNumber i)
      pure (ClassifiedIssue i c{ happened = merged })

  -- Filter out PRs that were closed without merging
  let (issues4, notMerged) = partition (happened . issueClass) issues3
  debugPrintIssues notMerged "PRs closed without merging"

  -- Filter out issues/PRs that have a bad label
  let (issues5, badLabel)  = partition (Set.null . badLabels . issueClass) issues4
  debugPrintIssues badLabel "Issues/PRs that have a label excluding them from the changelog"

  -- Print issues and PRs.

  let ms = Text.unpack mileStoneTitle
  if null issues5 then debugPrint $
    "No matching closed issues or PRs in milestone " ++ ms
  else do
    let (issues, prs) = partition (isIssue . issueClass) issues5
    debugPrintIssues issues $ "Issues for closed for milestone " ++ ms
    debugPrintIssues prs $ "PRs for closed for milestone " ++ ms
    forM_ issues $ \ ic -> putStrLn $ "- " ++ printIssue (theIssue ic)
    forM_ prs    $ \ ic -> putStrLn $ "- " ++ printIssue (theIssue ic)


-- | Crash on exception.
crashOr :: Show e => IO (Either e a) -> IO a
crashOr m = either (die . show) return =<< m
