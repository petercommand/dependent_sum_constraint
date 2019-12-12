import ./backend.nix
/*
let pkgs = import ./pkgs.nix {};
    libsnark = import ./libsnark.nix;
    agdaCS = import ./agda.nix;
    
    exclude_dir = ''
      /result
      /libsnark
    '';
in

pkgs.stdenv.mkDerivation {
   name = "dependent-sum-all";
   src = pkgs.nix-gitignore.gitignoreSource exclude_dir ./.;
   ARGS = "LitTest";
   builder = ./builder.sh;
   inherit (pkgs) AgdaStdlib;
   buildInputs = import ./build_input.nix { inherit pkgs; };
}*/
