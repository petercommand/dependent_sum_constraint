{ pkgs ? (import <nixpkgs>) {} }:
let
  nix_pri = pkgs.nix // { meta.priority = 0; };
  custom_pkgs = import (fetchTarball "https://github.com/NixOS/nixpkgs-channels/archive/4cd2cb43fb3a87f48c1e10bb65aee99d8f24cb9d.tar.gz") {};
in custom_pkgs // { nix = nix_pri; }
