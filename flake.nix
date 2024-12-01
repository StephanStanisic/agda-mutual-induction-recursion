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
              (texlive.withPackages(ps: [ps.droid]))
              
              nixpkgs-fmt
              coq
              coqPackages_8_19.coq-lsp
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
