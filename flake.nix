{
  description = "tekne.dev — personal website and blog";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            # 24.x matches the toolchain the lockfile was resolved against.
            pkgs.nodejs_24

            # Deploys to Firebase Hosting, and — more useful day to day —
            # provides `firebase emulators:start`, the only way to exercise
            # firebase.json's cleanUrls/redirects locally. `npm run preview`
            # serves through Vite and so silently ignores that config.
            pkgs.firebase-tools

            pkgs.bashInteractive
          ];

          shellHook = ''
            export SHELL="${pkgs.bashInteractive}/bin/bash"

            echo "tekne.dev dev shell"
            echo "  npm run dev                     dev server (hot reload)"
            echo "  npm run build                   static build into build/"
            echo "  npm run check                   svelte-check"
            echo "  npm run lint / npm run format   prettier + eslint"
            echo ""
            echo "  firebase emulators:start        serve build/ under the real"
            echo "                                  hosting rules (cleanUrls,"
            echo "                                  redirects) — run a build first"
            echo "  firebase deploy                 publish build/ to tekne.dev"
            echo ""
          '';
        };
      }
    );
}
