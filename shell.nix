let pkgs = import <nixpkgs> {};
    nix_pri = pkgs.nix // { meta.priority = 0; };
in
with import (fetchTarball "https://github.com/NixOS/nixpkgs-channels/archive/4cd2cb43fb3a87f48c1e10bb65aee99d8f24cb9d.tar.gz") {};
stdenvNoCC.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
#  PATH="/home/pancake/.local/bin";
  buildInputs = [
    haskellPackages.Agda
    gcc
    git
    cacert
    cmake
    boost
    gtest
    nix_pri
    openssl
    stack
    gmp
    gnumake
    ghc
    procps
    pkgconfig
    cabal-install
    pythonPackages.markdown
  ];
}

