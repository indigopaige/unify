{
  inputs = {
    flk.url = "github:numtide/flake-utils";
    qik.url = "github:indypaige/qik";
  };

  outputs        = { flk, qik, ... }:
    flk.lib.eachDefaultSystem (system: {
      packages.default = qik.lib.${system}.haskell.mk {
        name = "unify";
        root = ./.;
      };
    });
}
