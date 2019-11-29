let pkgs = import ./pkgs.nix {};
    libsnark = import ./libsnark.nix;
    exclude_dir = ''
      /result
      /libsnark
    '';
in
pkgs.stdenv.mkDerivation {
   name = "dependent-sum";
   src = pkgs.nix-gitignore.gitignoreSource exclude_dir ./.;
   ARGS = "LitTest";
   builder = ./builder.sh;
   inherit (pkgs) AgdaStdlib;
   buildInputs = import ./build_input.nix { inherit pkgs; } ++ [ pkgs.AgdaStdlib libsnark ];
}
