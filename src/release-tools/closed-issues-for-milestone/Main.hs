{-# LANGUAGE BlockArguments            #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RecordWildCards           #-}

module Main ( main ) where

import Control.Monad
import Data.Bifunctor (bimap)
import Data.Foldable
import Data.Functor
import Data.List (partition)
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.ByteString.Char8 as BS

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.Vector as V

import System.Environment ( getArgs, getEnv, getProgName )
import System.Exit        ( die )
import System.IO          ( hPutStrLn, stderr )

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

main :: IO ()
main = getArgs >>= \case
  "-h"     : _ -> usage
  "--help" : _ -> usage
  [arg]        -> run (Text.pack arg)
  _            -> usage

usage :: IO ()
usage = do
  progName <- getProgName
  putStrLn $ unlines
    [ "Usage: " ++ progName ++ " <milestone>"
    , ""
    , "Retrieves closed issues for the given milestone from github repository"
    , theRepo ++ " and prints them as markdown to stdout."
    , ""
    , "Expects an access token in environment variable GITHUB_TOKEN."
    ]

debugPrint :: String -> IO ()
debugPrint = hPutStrLn stderr

type Label = Text

issueLabelsNames :: Issue -> [Label]
issueLabelsNames i = map (untagName . labelName) $ V.toList $ issueLabels i

-- Please keep the labels in the list in alphabetic order!
labelsNotInChangelog :: Set Label
labelsNotInChangelog = Set.fromList
  [ "Makefile"
  , "agda-bisect"
  , "bug-tracker"
  , "closed-issues-for-milestone"
  , "debug"
  , "dev: hlint"
  , "devx"
  , "documented-in-changelog"
  , "faq"
  , "fix-agda-whitespace"
  , "haddock"
  , "hTags"
  , "infra: github workflows"
  , "infra: test suite"
  , "maculata"
  , "not-in-changelog"
  , "refactor"
  , "regression on master"
  , "release"
  , "repository"
  , "status: abandoned"
  , "status: duplicate"
  , "status: invalid"
  , "status: wontfix"
  , "status: working-as-intended"
  , "style"
  , "travis"
  , "type: question"
  , "type: task"
  , "typo"
  ]

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

-- | This classifies issue numbers,
--   but the field 'happened' is only set correctly for issues, not for milestones.
--
classifyIssue :: Id Milestone -> Issue -> Class
classifyIssue mileStoneId i = Class{..}
  where
  correctMilestone        = maybe False ((mileStoneId ==) . milestoneNumber) $ issueMilestone i
  isIssue                 = isNothing $ issuePullRequest i
  happened                = maybe True (StateReasonNotPlanned /=) $ issueStateReason i
  (badLabels, goodLabels) = bimap Set.fromList Set.fromList $
     partition (`Set.member` labelsNotInChangelog) $ issueLabelsNames i

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

debugPrintIssues :: [(Issue,Class)] -> String -> IO ()
debugPrintIssues is title =
  unless (null is) do
    debugPrint title
    forM_ is $ \ (i, _c) -> debugPrint $ "- " ++ printIssue i
    debugPrint ""


-- | Retrieve closed issues for the given milestone and print as csv to stdout.
run :: Text -> IO ()
run mileStoneTitle = do

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

  -- Classify issues.
  let issues0 :: [(Issue, Class)]
      issues0 = reverse (toList issueVector) <&> \ i -> (i, classifyIssue mileStoneId i)

  -- We progressively filter out issue numbers not included in changelog.

  -- Filter out issues/PRs with wrong milestone:
  let (issues1, wrongMilestone) = partition (correctMilestone . snd) issues0
  debugPrintIssues wrongMilestone "Issues/PR with wrong milestone:"

  -- Filter out issues that were "Closed as not planned"
  let (issues2, didNotHappen) = partition (happened . snd) issues1
  debugPrintIssues didNotHappen "Issues closed as not planned"

  -- Find out which PRs were closed without merging
  issues3 <- forM issues2 $ \ ic@(i, c) -> do
    if isIssue c then pure ic else do
      merged <- crashOr $ github auth $ isPullRequestMergedR (N owner) (N repo) (issueNumber i)
      pure (i, c { happened = merged })

  -- Filter out PRs that were closed without merging
  let (issues4, notMerged) = partition (happened . snd) issues3
  debugPrintIssues notMerged "PRs closed without merging"

  -- Filter out issues/PRs that have a bad label
  let (issues5, badLabel)  = partition (Set.null . badLabels . snd) issues4
  debugPrintIssues badLabel "Issues/PRs that have a label excluding them from the changelog"

  -- Print issues and PRs.

  let ms = Text.unpack mileStoneTitle
  if null issues5 then debugPrint $
    "No matching closed issues or PRs in milestone " ++ ms
  else do
    let (issues, prs) = partition (isIssue . snd) issues5
    debugPrintIssues issues $ "Issues for closed for milestone " ++ ms
    debugPrintIssues prs $ "PRs for closed for milestone " ++ ms
    forM_ issues $ \ ic -> putStrLn $ "- " ++ printIssue (fst ic)
    forM_ prs    $ \ ic -> putStrLn $ "- " ++ printIssue (fst ic)


-- | Crash on exception.
crashOr :: Show e => IO (Either e a) -> IO a
crashOr m = either (die . show) return =<< m
