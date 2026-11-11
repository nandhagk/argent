{
  description = "Argent: time functions derived from Gallina definitions, and big-O bounds on them";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/c9fe7d12cd78d1adcd12dd15e24432dde5b155a0";

  outputs =
    { self, nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];
      pkgsFor = system: import nixpkgs { inherit system; };
      # The stock Rocq 9.3 package set, so every dependency comes from the binary cache.
      rocqFor = system: (pkgsFor system).rocqPackages_9_3;
    in
    {
      packages = nixpkgs.lib.genAttrs systems (
        system:
        let
          pkgs = pkgsFor system;
          rocq = rocqFor system;
        in
        {
          # The installed theory `Argent`, for other flakes to depend on.
          default = rocq.mkRocqDerivation {
            pname = "argent";
            opam-name = "argent";
            version = "0.1.0";
            src = pkgs.lib.fileset.toSource {
              root = ./.;
              fileset = pkgs.lib.fileset.unions [
                ./dune-project
                ./theories
              ];
            };
            useDune = true;
            propagatedBuildInputs = [
              rocq.stdlib
              rocq.rocq-elpi
            ];
          };
        }
      );

      devShells = nixpkgs.lib.genAttrs systems (
        system:
        let
          pkgs = pkgsFor system;
          rocq = rocqFor system;
          # The OCaml package set that this Rocq was built with.
          ocaml = rocq.rocq-core.ocamlPackages;
        in
        {
          default = pkgs.mkShell {
            packages = [
              rocq.rocq-core
              # Rocq 9 ships its standard library as a separate package found through ROCQPATH.
              rocq.stdlib
              rocq.rocq-elpi
              ocaml.ocaml
              ocaml.findlib
              ocaml.dune_3
              pkgs.just
              pkgs.git
            ];
            # A host library path would shadow the Nix store paths of the pinned toolchain.
            shellHook = ''
              unset LD_LIBRARY_PATH
            '';
          };
        }
      );

      formatter = nixpkgs.lib.genAttrs systems (system: (pkgsFor system).nixfmt);
    };
}
