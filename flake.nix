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
              pkgs.nodejs_22
              pkgs.jq
            ];
          };
        });
    };
}
