{-# LANGUAGE OverloadedStrings, ScopedTypeVariables #-}
module Main where

import Control.Exception
import Control.Monad


import qualified Data.Text as T
import qualified Data.Text.IO as T

import System.Directory

dropLast :: [a] -> [a]
dropLast [] = []
dropLast [x] = []
dropLast (x:xs) = x : dropLast xs

main :: IO ()
main = do
  cwd <- getCurrentDirectory
  agdaBuildExists <- doesFileExist "agda-build"
  when (not agdaBuildExists) $
    copyFile "stack-build-tmp" "stack-build"
  agdaBuild <- T.readFile "agda-build"
  stackBuildTmp <- T.readFile "stack-build-tmp"
  let findLink r@(x:xs) = length (filter (== "Linking") r) /= 0
      findLink _ = False
  when (any findLink $ map T.words $ T.lines stackBuildTmp) $
    copyFile "stack-build-tmp" "stack-build"
  stackBuild <- T.readFile "stack-build"
  let linkExe' = filter findLink $ map T.words $ T.lines $ stackBuild
  case linkExe' of
    (linkExe : _) -> do
       { T.putStrLn $ T.append "Found link exe path: " $ linkExe !! 1
       ; let linkPath = T.append (T.intercalate "/" $ dropLast $ T.split (== '/') (linkExe !! 1) ) "/"
             modOriPath = map (!! 5) $ filter (\x -> head x == "Compiling") $ map T.words $ filter (\x -> T.length x /= 0) $ T.lines agdaBuild
             modTruncatePrefix = map (T.intercalate "/" . drop (1 + (length $ filter (\x -> T.length x /= 0) $ T.split (== '/') $ T.pack $ cwd)) . T.split (== '/')) modOriPath
             rtePath = T.append linkPath "dependent-sum-tmp/MAlonzo/RTE"
             modPath = rtePath : map (T.append linkPath . T.append "dependent-sum-tmp/" . T.intercalate "/" . dropLast . T.split (== '.')) modTruncatePrefix
             rm path = do
                { T.putStrLn $ T.append "Removing file: " path
                ; removeFile (T.unpack path) `catch` \ (SomeException _) -> return ()
                }
       ; sequence $ map (\x -> do
           T.putStrLn (T.append "Changed target: " x)
           sequence_ $ map rm (map (T.append x) [ ".hi", ".o", ".p_o", ".p_hi" ]) ) modPath 
       ; return ()
       }
    _ -> T.putStrLn $ "Link exe path not found"
