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
            pkgs.pnpm

            # Deploys to Firebase Hosting, and — more useful day to day —
            # provides `firebase emulators:start`, the only way to exercise
            # firebase.json's cleanUrls/redirects locally. `pnpm preview`
            # serves through Vite and so silently ignores that config.
            # tests/hosting.test.mjs drives this, so `pnpm test` needs the shell.
            pkgs.firebase-tools

            # Lean toolchain manager. elan reads each project's lean-toolchain
            # and fetches the matching Lean, so the version is pinned by the
            # repo rather than by whatever nixpkgs happens to ship.
            pkgs.elan

            pkgs.bashInteractive
          ];

          shellHook = ''
            export SHELL="${pkgs.bashInteractive}/bin/bash"

            echo "tekne.dev dev shell"
            echo "  pnpm dev                        dev server (hot reload)"
            echo "  pnpm build                      static build into build/"
            echo "  pnpm test                       build, then CAS + hosting tests"
            echo "  pnpm check                      svelte-check"
            echo "  pnpm lint / pnpm format         prettier + eslint"
            echo "  pnpm lean                       build every Lean dev under lean/"
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
