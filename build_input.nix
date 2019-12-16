{ pkgs }:
with pkgs;
[
    haskellPackages.Agda
    gcc
    git
    cacert
    cmake
    boost
    gtest
    nix
    openssl
    stack
    gmp
    gnumake
    (haskellPackages.ghcWithPackages (p: [ p.text p.ieee754 p.containers p.arithmoi ]))
    procps
    pkgconfig
    cabal-install
    pythonPackages.markdown
    glibcLocales
]

