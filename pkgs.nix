{ pkgs ? (import <nixpkgs>) {} }:
let
  nix_pri = pkgs.nix // { meta.priority = 0; };
  z3new = pkgs.z3.overrideDerivation (attrs: {
        name = "z3-4.8.7";
        version = "4.8.7";
        src = pkgs.fetchFromGitHub {
          owner  = "Z3Prover";
          repo   = attrs.pname;
          rev    = "84025d5c116b5da480f1e658e08029ef5b613886";
          sha256 = "01l9dlmsb79ynhiigajbrc1hywn8dl3q38cz6dshd15a5g0s3q20";
        };
    });
  custom_pkgs = import (fetchTarball "https://github.com/NixOS/nixpkgs-channels/archive/4cd2cb43fb3a87f48c1e10bb65aee99d8f24cb9d.tar.gz") {};
in custom_pkgs // { z3 = z3new; nix = nix_pri; }
