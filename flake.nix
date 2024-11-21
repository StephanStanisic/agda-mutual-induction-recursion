{
  description = "foo";

  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let pkgs = import nixpkgs {
          inherit system;
        }; in
        {
          devShells.default = pkgs.mkShell {
            packages = with pkgs; [
              pandoc
              texliveFull
              nixpkgs-fmt
            ];
            buildInputs = with pkgs; [
              (agda.withPackages (ps: [
                ps.standard-library
              ]))
            ];
          };
        }
      );
}
