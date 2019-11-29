let pkgs = import ./pkgs.nix {};
    exclude_dir = ''
      /result
      /libsnark
    '';
    ARGS = "LitTest";
    agdaDrv = pkgs.stdenv.mkDerivation {
      name = "dependent-sum-agda";
      src = pkgs.nix-gitignore.gitignoreSource exclude_dir ./.;
      ARGS = "LitTest";
      builder = ./builder.sh;
      inherit (pkgs) AgdaStdlib;
      buildInputs = import ./build_input.nix { inherit pkgs; } ++ [ pkgs.AgdaStdlib ];
   };
   createBuilder = pkgs.writeTextFile {
     name = "createBuilder";
     text = ''
       #!/bin/sh
       source $stdenv/setup
       mkdir -p $out
       cp -r $agdaDrv/* .
       chmod -R 755 *
       ghc -i$./ -Werror ./MAlonzo/Code/Test/$ARGS.hs -main-is MAlonzo.Code.Test.$ARGS --make -fwarn-incomplete-patterns -fno-warn-overlapping-patterns -o $out/$name
     '';
     executable = true;
     destination = "/builder.sh";
   };

in
pkgs.stdenv.mkDerivation {
  name = "dependent-sum";
  builder = "${createBuilder}/builder.sh";
  inherit agdaDrv ARGS;
  unpackPhase = true;
  buildInputs = import ./build_input.nix { inherit pkgs; } ++ [ agdaDrv ];
}