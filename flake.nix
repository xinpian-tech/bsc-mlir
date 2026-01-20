{
  description = "GAA (Guard Atomic Action) - Bluespec Compiler rewritten in MLIR with CIRCT";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    treefmt-nix.url = "github:numtide/treefmt-nix";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    typix = {
      url = "github:loqusion/typix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs @ {
    self,
    nixpkgs,
    flake-parts,
    treefmt-nix,
    rust-overlay,
    typix,
    ...
  }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      systems = ["x86_64-linux" "aarch64-linux"];

      imports = [
        treefmt-nix.flakeModule
      ];

      perSystem = {
        config,
        pkgs,
        system,
        ...
      }: let
        overlay = import ./nix/overlay.nix;
        customPkgs = pkgs.extend overlay;
        bsc-original = pkgs.callPackage ./nix/pkgs/bsc.nix {
          version = "1.0";
        };

        # Rust toolchain with nightly for edition 2024
        rustPkgs = pkgs.extend rust-overlay.overlays.default;
        rustToolchain = rustPkgs.rust-bin.nightly.latest.default;
        rustPlatform = pkgs.makeRustPlatform {
          cargo = rustToolchain;
          rustc = rustToolchain;
        };

        # BSC Rust frontend package
        bsc-rust = rustPlatform.buildRustPackage {
          pname = "bsc-rust";
          version = self.shortRev or self.dirtyShortRev or "dirty";
          src = ./bsc-rust;
          cargoLock.lockFile = ./bsc-rust/Cargo.lock;
          # Skip tests for now during initial development
          doCheck = false;
        };

        # Testbenchs (generated from BSC testsuite)
        # testDefs: pure data (test definitions)
        # testbenchLib: build functions
        testDefs = import ./nix/testbenchs.nix;
        testbenchLib = import ./nix/testbench-lib.nix {
          inherit (pkgs) lib callPackage circt jq;
          bsv-json = customPkgs.bsv-json;
          gaa-mlir = customPkgs.gaa-mlir;
          bsc = bsc-original;
          testsuiteSrc = ./vendor/bsc/testsuite;
        };
        # All tests with bsc-result and diff-test attributes
        allTests = testbenchLib.buildAllTestAttrs testDefs;

        testbenchs = allTests // {
          # Aggregated tests (all active tests through each stage)
          all-bsv-roundtrip = testbenchLib.buildAllRoundtripTest testDefs;
          all-mlir-import = testbenchLib.buildAllMlirImportTest testDefs;
          all-schedule-verify = testbenchLib.buildAllScheduleVerifyTest testDefs;
          all-verilog = testbenchLib.buildAllVerilogTest testDefs;

          # Metadata
          stats = testbenchLib.getStats testDefs;
          testNames = builtins.attrNames testDefs;
        };

        # Typst documentation build
        typixLib = typix.lib.${system};
        docSrc = typixLib.cleanTypstSource ./doc;

        # Typst packages used by our documents
        # Dependencies: fletcher -> cetz -> oxifmt
        typstPackages = [
          {
            name = "fletcher";
            version = "0.5.8";
            hash = "sha256-kKVp5WN/EbHEz2GCTkr8i8DRiAdqlr4R7EW6drElgWk=";
          }
          {
            name = "cetz";
            version = "0.3.4";
            hash = "sha256-T0tajTEdUZ50mUCnZv5QUh5AwEESnhyRrwxC5h8wdRQ=";
          }
          {
            name = "oxifmt";
            version = "0.2.1";
            hash = "sha256-FvrCkjAyxZcn3gHoTULKxF6HkNoo31bv/KSfTeQbCdk=";
          }
        ];

        # Common args for all document builds
        typstCommonArgs = {
          fontPaths = [
            "${pkgs.liberation_ttf}/share/fonts/truetype"
          ];
        };

        # Build a single typst document
        buildTypstDoc = name:
          typixLib.buildTypstProject (typstCommonArgs
            // {
              src = docSrc;
              typstSource = "${name}.typ";
              unstable_typstPackages = typstPackages;
            });

        # All document names (without .typ extension)
        docNames = [
          "ASyntaxJson"
          "BSVImport"
          "GAARational"
          "IR"
          "MLIRPass"
          "patent-7647567"
          "Scheduling"
          "SchedulePassPlan"
        ];

        # Build all documents as a single derivation
        allDocs = pkgs.runCommand "gaa-docs" {} ''
          mkdir -p $out
          ${builtins.concatStringsSep "\n" (map (name: ''
            cp ${buildTypstDoc name} $out/${name}.pdf
          '') docNames)}
        '';

        # Watch script for document development
        docWatchScript = typixLib.watchTypstProject (typstCommonArgs
          // {
            typstSource = "Scheduling.typ";
          });
      in {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          config.allowUnfree = true;
        };

        packages =
          {
            default = customPkgs.gaa-mlir;
            gaa-mlir = customPkgs.gaa-mlir;
            bsv-json = customPkgs.bsv-json;
            inherit bsc-original bsc-rust;
            docs = allDocs;
          }
          // builtins.listToAttrs (map (name: {
            name = "doc-${name}";
            value = buildTypstDoc name;
          }) docNames);

        # Export testbenchs via legacyPackages for direct access
        # Usage: nix build .#testbenchs.<testname>.schedule-verify
        legacyPackages = {
          inherit testbenchs;
        };

        devShells.default = pkgs.mkShell {
          name = "gaa-dev";
          packages = with pkgs; [
            # Build tools
            cmake
            ninja
            pkg-config

            # CIRCT (includes MLIR/LLVM)
            circt

            # SMT solver for disjoint analysis
            z3

            # JSON library (for bsv-json build)
            nlohmann_json

            # BSV JSON library
            customPkgs.bsv-json

            # Development tools
            clang-tools
            lit

            # Debugging
            gdb

            # IDE config generation
            python3
          ];

          shellHook = ''
            export CIRCT_DIR="${pkgs.circt.dev}/lib/cmake/circt"
            export MLIR_DIR="${pkgs.circt.llvm.dev}/lib/cmake/mlir"
            export LLVM_DIR="${pkgs.circt.llvm.dev}/lib/cmake/llvm"
            export MLIR_TABLEGEN_EXE="${pkgs.circt.llvm}/bin/mlir-tblgen"
            export LLVM_EXTERNAL_LIT="${pkgs.lit}/bin/lit"
            export Z3_DIR="${pkgs.z3.dev}/lib/cmake/z3"
            export bsv_json_DIR="${customPkgs.bsv-json}/lib/cmake/bsv-json"
            echo "GAA development environment (CIRCT ${pkgs.circt.version})"
            echo "CIRCT_DIR: $CIRCT_DIR"
            echo "MLIR_DIR: $MLIR_DIR"
            echo "LLVM_DIR: $LLVM_DIR"
            echo "Z3_DIR: $Z3_DIR"
            echo "bsv_json_DIR: $bsv_json_DIR"

            # Generate IDE configuration files
            python3 scripts/generate-clangd-config.py
          '';
        };

        # Alias for gaa-mlir development
        devShells.gaa-mlir = config.devShells.default;

        devShells.bsc = let
          ghcWithPackages = pkgs.ghc.withPackages (g: with g; [
            old-time
            regex-compat
            syb
            split
            aeson
            aeson-pretty
          ]);
          yices-src = pkgs.fetchurl {
            url = "https://github.com/B-Lang-org/bsc/releases/download/2024.07/yices-src-for-bsc-2024.07.tar.gz";
            sha256 = "sha256-pyEdCJvmgwOYPMZEtw7aro76tSn/Y/2GcKTyARmIh4E=";
          };
        in pkgs.mkShell {
          name = "bsc-dev";
          packages = with pkgs; [
            # Haskell
            ghcWithPackages

            # Build tools
            automake
            autoconf
            bison
            flex
            gperf
            perl
            pkg-config
            gnumake

            # Runtime dependencies
            fontconfig
            xorg.libX11
            tcl
            tk
            xorg.libXft
            zlib
            which

            # Testing
            gmp
            iverilog
          ];

          YICES_SRC = yices-src;
          LDCONFIG = "ldconfig";

          shellHook = ''
            echo "BSC development environment"
            echo "Working directory: vendor/bsc"
            echo "YICES_SRC: $YICES_SRC"
            echo ""
            echo "Setup yices (required once):"
            echo "  tar -C vendor/bsc -xf \$YICES_SRC"
            echo ""
            echo "Build:"
            echo "  cd vendor/bsc && make NO_DEPS_CHECKS=1 NOGIT=1 STP_STUB=1 LDCONFIG=ldconfig install-src"
          '';
        };

        devShells.doc = typixLib.devShell {
          inherit (typstCommonArgs) fontPaths;
          packages = [
            docWatchScript
            pkgs.typstyle
            pkgs.tinymist
          ];
        };

        # Development shell for bsc-rust (no bsc-frontend dependency for fast iteration)
        devShells.bsc-rust = pkgs.mkShell {
          name = "bsc-rust-dev";
          packages = [
            rustToolchain
            pkgs.rust-analyzer
            bsc-original
          ];
          BSC_LIBRARIES_DIR = "${self}/src/Libraries";
          BSC_PATH = "${bsc-original}/bin/bsc";
          shellHook = ''
            echo "BSC Rust Frontend Development Environment (Rust 2024 Edition)"
            echo ""
            echo "Commands:"
            echo "  cargo build    - Build all crates"
            echo "  cargo check    - Type check all crates"
            echo "  cargo test     - Run tests"
            echo "  cargo clippy   - Run linter"
            echo ""
            echo "Environment:"
            echo "  BSC_LIBRARIES_DIR=$BSC_LIBRARIES_DIR"
            echo "  BSC_PATH=$BSC_PATH"
            echo ""
          '';
        };

        treefmt = {
          projectRootFile = "flake.nix";
          programs = {
            nixfmt.enable = true;
          };
          settings.formatter = {
            clang-format = {
              command = "${pkgs.clang-tools}/bin/clang-format";
              options = ["-i"];
              includes = [
                "gaa-mlir/**/*.cpp"
                "gaa-mlir/**/*.h"
                "gaa-mlir/**/*.hpp"
                "gaa-mlir/**/*.c"
                "gaa-mlir/**/*.cc"
                "gaa-mlir/**/*.td"
              ];
            };
          };
        };
      };
    };
}
