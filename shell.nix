let pkgs = import ./pkgs.nix {};
in
with pkgs;
stdenvNoCC.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = import ./build_input.nix { inherit pkgs; };
}

