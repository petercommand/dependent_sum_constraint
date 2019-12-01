let pkgs = import ./pkgs.nix {};
in
with pkgs;
stdenv.mkDerivation rec {
  name = "libsnark";
  src = pkgs.nix-gitignore.gitignoreSource "/build\n" ./libsnark;
  buildInputs = import ./build_input.nix { inherit pkgs; };
}
