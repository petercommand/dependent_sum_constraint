let pkgs = import ./pkgs.nix {};
    libsnark = import ./libsnark.nix;
    agdaCS = import ./agda.nix;
    exclude_dir = ''
      /result
      /libsnark
      /agda
    '';
   createBuilder = pkgs.writeTextFile {
     name = "dependent-sum-backend-builder";
     text = ''
       #!/bin/sh
       source $stdenv/setup
       mkdir -p $out
       cp -r ${agdaCS}/* $out/
       echo $PWD
       g++ -Wno-unused-variable -DBINARY_OUTPUT -DBN_SUPPORT_SNARK=1 -DCURVE_BN128 -DMONTGOMERY_OUTPUT -DUSE_ASM -I${libsnark}/include -I${libsnark}/include/libff -std=c++11 -Wall -Wextra -Wfatal-errors -ggdb3 -O2 -march=native -mtune=native -O2 -g -DNDEBUG -c $src/main.cpp -o main.o
       g++ -g main.o ${libsnark}/lib/libsnark.a -lgmp -lgmpxx ${libsnark}/lib/libff.a -lcrypto -lprocps -o $out/main
       $out/main ${agdaCS}/constraints_serialize ${agdaCS}/solve.result
     '';
     executable = true;
     destination = "/builder.sh";
   };

in
pkgs.stdenv.mkDerivation {
   name = "dependent-sum-backend";
   src = pkgs.nix-gitignore.gitignoreSource exclude_dir ./backend_interface;
   builder = "${createBuilder}/builder.sh";
   buildInputs = import ./build_input.nix { inherit pkgs; } ++ [ pkgs.AgdaStdlib libsnark ];
}
