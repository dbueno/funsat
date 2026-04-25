{
  description = "funsat";

  inputs.nixpkgs.url = "nixpkgs";

  outputs = { self, nixpkgs }:
    let
      supportedSystems = [ "x86_64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs supportedSystems (system: f system);
      pkgsFor = forAllSystems (system:
        import nixpkgs {
          inherit system;
          overlays = [ self.overlays.default ];
        });
    in
    {
      overlays.default = final: prev:
        let
          hp = prev.haskellPackages.override {
            overrides = prev.lib.composeExtensions
              (_self: _super: { })
              (self': _super: {
                bitset = self'.callCabal2nix "bitset" ./etc/bitset { };
                parse-dimacs = self'.callCabal2nix "parse-dimacs" ./etc/parse-dimacs { };
                funsat = self'.callCabal2nix "funsat" ./. { };
              });
          };
        in
        {
          haskellPackages = hp;
        };

      packages = forAllSystems (system: {
        default = pkgsFor.${system}.haskellPackages.funsat;
        funsat = pkgsFor.${system}.haskellPackages.funsat;
      });

      checks = forAllSystems (system: {
        inherit (self.packages.${system}) funsat;
      });

      devShells = forAllSystems (system:
        let
          pkgs = pkgsFor.${system};
          hp = pkgs.haskellPackages;
        in
        {
          default = hp.shellFor {
            packages = p: [ p.funsat ];
            withHoogle = false;
            buildInputs = [
              pkgs.cabal-install
              hp.ghcid
            ];
          };
        });
    };
}
