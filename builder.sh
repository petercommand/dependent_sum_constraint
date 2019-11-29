#!/bin/sh
source $stdenv/setup
cp -r $src/* .
chmod -R 755 *
rm agda/.agda-lib
make nix ARGS=$ARGS -C agda
mkdir $out
cp -r agda/MAlonzo $out/

