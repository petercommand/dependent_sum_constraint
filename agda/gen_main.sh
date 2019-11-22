#!/bin/sh

echo "module Main where" > Main.hs
echo "import qualified MAlonzo.Code.Test.$1 as Test" >> Main.hs
echo "main :: IO ()" >> Main.hs
echo "main = Test.main" >> Main.hs
