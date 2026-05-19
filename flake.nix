{
  description = "Explore JS compile targets of Dafny, Agda, and Idris2";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system);
    in
    {
      devShells = forAllSystems (system:
        let pkgs = import nixpkgs { inherit system; };
        in {
          default = pkgs.mkShell {
            packages = [
              pkgs.dafny
              pkgs.agda
              pkgs.idris2
              # Coq pinned to the version agoric-labs/jesc24 targets (8.9.1).
              # The OCaml + js_of_ocaml below are *separate* — they compile
              # Coq's extracted .ml output, and don't need to match the OCaml
              # used to build Coq itself.
              pkgs.coq_8_9
              pkgs.ocaml
              pkgs.ocamlPackages.findlib
              pkgs.ocamlPackages.js_of_ocaml
              pkgs.ocamlPackages.js_of_ocaml-compiler
              pkgs.nodejs_22
              pkgs.jq
            ];
          };
        });
    };
}
