{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Exception
import Control.Monad


import qualified Data.Text as T
import qualified Data.Text.IO as T

import System.Directory
import System.Exit
import System.Process
import System.Posix.Env
data RunResult = RunSuccess T.Text | RunFailed T.Text deriving (Show)

isSuccess (RunSuccess _) = True
isSuccess _ = False

main :: IO ()
main = do
  cwd <- getCurrentDirectory
  setEnv "AGDA_DIR" cwd True
  tests <- fmap (map (T.intercalate "." . init) . filter (\x -> last x == "agda") . map (T.split (== '.') . T.pack))
             $ listDirectory "agda/Test/"
  putStrLn $ show $ tests
  r <- forM tests $ \t -> do
    (_, _, _, handle) <- createProcess (shell $ T.unpack $ "make ARGS=" <> t <> " && make exec")
    code <- waitForProcess handle
    case code of
      ExitSuccess -> return $ RunSuccess t
      ExitFailure _ -> return $ RunFailed t
  let failures = filter (not . isSuccess) r
  when (length failures /= 0) $
    exitWith (ExitFailure 1)