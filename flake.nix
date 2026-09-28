{
  description = "verus-spec-check: Automated testing of Verus contracts, paired with the matching Verus binary.";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # Pin the verus version that matches the overlay + version pins
        verusVersion = "0.2026.09.27.3cf1832";

        # Additional pinned verus releases, exposed as packages
        # (`nix build .#verus-0308`) and dev shells
        # (`nix develop .#verus-0308`)
        extraVerusVersions = {
          "verus-0308" = "0.2026.03.08.23dc6e7";
        };

        platform =
          if system == "x86_64-linux" then "x86-linux"
          else if system == "aarch64-darwin" then "arm64-macos"
          else if system == "x86_64-darwin" then "x86-macos"
          else throw "Unsupported system: ${system}";

        # SHA-256 hashes for each platform's release zip
        srcHashes = {
          "0.2026.09.27.3cf1832" = {
            "arm64-macos" = "sha256-SVvn9OYnAT7pgeOrRYZVsy58ZnyIoxh2SIHjEnR/6dw=";
            "x86-linux" = "sha256-pSyWBWB6zS2ceKvQBeegVfUbReQj+aTL8u2LGYY4zwM=";
            "x86-macos" = "sha256-C+my6Ol1d/tIQbgGY69f0JX+SvtXlIzEtS1zT2Jfs80=";
          };
          "0.2026.03.08.23dc6e7" = {
            "arm64-macos" = "";
            "x86-linux" = "";
            "x86-macos" = "";
          };
        };

        # z3 pinned to the version rust_verify's solver check expects.
        # Maintained by tools/release/flake-bump.sh from upstream's
        # source/tools/get-z3.sh. Reuses the nixpkgs binary when versions
        # match, otherwise builds from the tagged source.
        z3Version = "4.16.0";
        z3 =
          if pkgs.z3.version == z3Version then pkgs.z3
          else pkgs.z3.overrideAttrs (old: {
            version = z3Version;
            src = pkgs.fetchFromGitHub {
              owner = "Z3Prover";
              repo = "z3";
              tag = "z3-${z3Version}";
              hash = "sha256-DnhX3kxggnFmyYwXEPBsBA1rh4oor1oIJR5TMJk/jvc=";
            };
          });

        mkVerus = version: pkgs.stdenv.mkDerivation {
          pname = "verus";
          inherit version;

          src = pkgs.fetchzip {
            url = "https://github.com/verus-lang/verus/releases/download/release%2F${version}/verus-${version}-${platform}.zip";
            sha256 = srcHashes.${version}.${platform} or "";
          };

          # Pre-built release; no build step needed. We just install
          # the contents and put wrapper scripts in $out/bin that exec
          # the real binaries with their original location preserved.
          # Verus's binary uses its own location to find sibling
          # files (`libvstd.rlib`, `libverus_builtin_macros.dylib`,
          # etc.), so a plain symlink in $out/bin breaks the lookup.
          # The wrapper scripts keep the binaries in $out/ where verus
          # finds its companions.
          nativeBuildInputs = [ pkgs.makeWrapper ];

          installPhase = ''
            mkdir -p $out/share/verus
            cp -r $src/* $out/share/verus/
            chmod -R u+w $out/share/verus
            # build-only cruft
            rm -rf $out/share/verus/build $out/share/verus/incremental \
                   $out/share/verus/.fingerprint
            # always the nix z3, whether or not the zip shipped one
            rm -f $out/share/verus/z3
            ln -s ${z3}/bin/z3 $out/share/verus/z3
            mkdir -p $out/bin
            for bin in verus cargo-verus rust_verify; do
              if [ -f "$out/share/verus/$bin" ]; then
                makeWrapper $out/share/verus/$bin $out/bin/$bin \
                  --set-default VERUS_Z3_PATH ${z3}/bin/z3
              fi
            done
            ln -s ${z3}/bin/z3 $out/bin/z3
          '';
        };

        # The primary verus binary, pinned to verusVersion. The refactor to
        # mkVerus/extraVerusVersions left this binding out, which made every
        # reference to `verus` below undefined; restore it here.
        verus = mkVerus verusVersion;

        # Common build inputs for the dev shell.
        commonBuildInputs = [
          verus
          pkgs.rustup
          pkgs.pkg-config
          pkgs.cargo-expand
          # tools/check_versions.sh is a zsh script. Providing zsh here
          # means CI doesn't need `apt-get install zsh` on every run.
          pkgs.zsh
          # llvm-profdata / llvm-cov for `#[vcheck_cov_fuzz]`'s
          # external-target (assume_specification) coverage measurement.
          pkgs.rustc.llvmPackages.llvm
        ];

      in {
        # `nix run .#verus`: invokes the verus binary directly.
        # `nix run .#sweep`: runs run_examples.sh.
        # `nix run .#check`: runs version + overlay checks.

        packages = {
          default = verus;
          inherit verus;

          sweep = pkgs.writeShellApplication {
            name = "verus-spec-check-sweep";
            runtimeInputs = commonBuildInputs;
            text = ''
              cd ${self}
              echo "verus version: $(verus --version 2>&1 | head -1)"
              bash tools/run_examples.sh
            '';
          };

          check = pkgs.writeShellApplication {
            name = "verus-spec-check-check";
            runtimeInputs = commonBuildInputs;
            text = ''
              cd ${self}
              echo "=== version pin check ==="
              zsh tools/check_versions.sh || true
              echo
              echo "=== overlay drift check ==="
              zsh tools/check_overlay.sh
            '';
          };
        };

        devShells.default = pkgs.mkShell {
          buildInputs = commonBuildInputs;

          shellHook = ''
            export RUSTUP_TOOLCHAIN=$(sed -n 's/.*"toolchain"[^"]*"\([^" ]*\).*/\1/p' ${verus}/share/verus/version.json)
            echo "verus-spec-check dev shell ready."
            echo "  rustc:         $(rustc --version)"
            echo "  verus version: $(verus --version 2>&1 | head -1)"
            # Kani isn't in nixpkgs (its release bundles a pinned rustup
            # toolchain + CBMC), so the `mode = "kani"` proof tier needs a
            # one-time host install. Surface the status here so a missing
            # kani is discovered at shell entry, not mid-test-run.
            if command -v cargo-kani >/dev/null 2>&1; then
              echo "  kani:          $(cargo kani --version 2>&1 | head -1)"
            else
              echo "  kani:          not installed (mode=\"kani\" proofs need it:"
              echo "                 cargo install --locked kani-verifier && cargo kani setup)"
            fi
            echo
            echo "Quick commands:"
            echo "  cargo build                      - build the workspace"
            echo "  cargo test -p verus_spec_check_test     - end-to-end verus-spec-check evaluation suite"
            echo "  cargo test -p verus_spec_check_engine   - verus-spec-check engine unit tests"
            echo "  bash tools/run_examples.sh       - run the documentation examples"
            echo "  zsh tools/check_versions.sh      - check version-pin consistency"
            echo "  cargo verus verify               - verify a project (run from a project dir)"
          '';
        };
      });
}
