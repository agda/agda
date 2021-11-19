{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE OverloadedStrings         #-}

module Main ( main ) where

import Data.Foldable
-- import Data.List ( intercalate )
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.ByteString.Char8 as BS

import qualified Data.Vector as V

import System.Environment ( getArgs, getEnv, getProgName )
import System.Exit        ( die )

import GitHub.Auth ( Auth( OAuth ) )

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
         , issueTitle
         )
  )

import GitHub.Data.Name ( Name( N ), untagName )
import GitHub.Data.Milestone ( Milestone( milestoneNumber, milestoneTitle ) )
import GitHub.Data.Options ( stateClosed )
import GitHub.Data.Request ( FetchCount(FetchAll) )

import GitHub.Endpoints.Issues.Milestones ( milestonesR )
import GitHub.Endpoints.Issues ( issuesForRepoR )

import GitHub.Request ( github )

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

issueLabelsNames :: Issue -> [Text]
issueLabelsNames i = map (untagName . labelName) $ V.toList $ issueLabels i

-- Please keep the labels in the list in alphabetic order!
labelsNotInChangelog :: [Text]
labelsNotInChangelog =
  [ "Makefile"
  , "agda-bisect"
  , "benchmark-suite"
  , "bug-tracker"
  , "closed-issues-for-milestone"
  , "devx"
  , "debug"
  , "documented-in-changelog"
  , "faq"
  , "fix-agda-whitespace"
  , "github-workflows"
  , "haddock"
  , "not-in-changelog"
  , "regression on master"
  , "repository"
  , "status: abandoned"
  , "status: duplicate"
  , "status: invalid"
  , "status: wontfix"
  , "status: working-as-intended"
  , "style"
  , "travis"
  , "type: task"
  , "typo"
  ]

-- | Retrieve closed issues for the given milestone and print as csv to stdout.
run :: Text -> IO ()
run mileStoneTitle = do

  -- Get authentication token from environment.
  auth <- OAuth . BS.pack <$> getEnv envGHToken

  -- Log in to repo.

  -- Resolve milestone into milestone id.
  mileStoneVector <- crashOr $ github auth (milestonesR (N owner) (N repo) FetchAll)
  mileStoneId <- case filter ((mileStoneTitle ==) . milestoneTitle) $ toList mileStoneVector of
    []  -> die $ "Milestone " ++ Text.unpack mileStoneTitle ++ " not found in github repo " ++ theRepo
    [m] -> return $ milestoneNumber m
    _   -> die $ "Milestone " ++ Text.unpack mileStoneTitle ++ " ambiguous in github repo " ++ theRepo

  -- Debug.
  -- print mileStoneId

  -- Get list of issues. GitHub's REST API v3 considers every pull
  -- request an issue. For this reason we get a list of both issues
  -- and pull requests when using the function 'issuesForRepo''.
  issueVector <- crashOr $ github auth (issuesForRepoR (N owner) (N repo) stateClosed FetchAll)
    -- Symbols not exported.
    -- IssueRepoMod $ \ o ->
    --   o { issueRepoOptionsMilestone = FilterBy mileStoneId
    --     , issueRepoOptionsState     = Just StateClosed
    --     }

  -- Filter by issues, milestone and labels.
  let issues :: [Issue]
      issues = reverse
        [ i
        | i <- filter (isNothing . issuePullRequest) $ toList issueVector
        , m <- maybeToList $ issueMilestone i
        , milestoneNumber m == mileStoneId
        , not $ any (`elem` issueLabelsNames i) labelsNotInChangelog
        ]

  -- Print issues.

  forM_ issues $ \ Issue{ issueNumber, issueTitle } -> do
    let n = unIssueNumber issueNumber
    putStrLn $
      "  [#" ++ show n
     ++ "](https://github.com/" ++ theRepo ++ "/issues/" ++ show n
     ++ "): " ++ Text.unpack issueTitle

  -- TODO: output tsv
  --
  -- forM_ issues $ \ Issue{ issueNumber, issueTitle } -> do
  --   putStrLn $ intercalate "\t" $
  --     [ show issueNumber
  --     , Text.unpack issueTitle
  --     ]

-- | Crash on exception.
crashOr :: Show e => IO (Either e a) -> IO a
crashOr m = either (die . show) return =<< m
