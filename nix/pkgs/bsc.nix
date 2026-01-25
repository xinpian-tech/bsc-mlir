{
  lib,
  stdenv,
  fetchurl,
  autoconf,
  automake,
  fontconfig,
  gperf,
  libX11,
  perl,
  flex,
  bison,
  pkg-config,
  tcl,
  tk,
  xorg,
  yices,
  zlib,
  ghc,
  gmp,
  iverilog,
  which,
  makeBinaryWrapper,
  targetPackages,
  version,
}:

let
  ghcWithPackages = ghc.withPackages (
    g: with g; [
      old-time
      regex-compat
      syb
      split
      aeson
      aeson-pretty
    ]
  );

  yices-src = fetchurl {
    url = "https://github.com/B-Lang-org/bsc/releases/download/2024.07/yices-src-for-bsc-2024.07.tar.gz";
    sha256 = "sha256-pyEdCJvmgwOYPMZEtw7aro76tSn/Y/2GcKTyARmIh4E=";
  };

  filteredSrc = lib.cleanSourceWith {
    src = ../..;
    filter = path: type:
      let
        relPath = lib.removePrefix (toString ../.. + "/") (toString path);
        isRustDir = lib.hasPrefix "bsc-rust" relPath;
      in
        !isRustDir;
  };
in
stdenv.mkDerivation {
  pname = "bsc-original";
  inherit version;

  src = filteredSrc;

  enableParallelBuilding = true;


  postUnpack = ''
    tar -C $sourceRoot/ -xf ${yices-src}
    chmod -R +rwX $sourceRoot/src/vendor/yices/v2.6/yices2
  '';

  postPatch = ''
    patchShebangs \
      src/vendor/stp/src/AST/genkinds.pl \
      src/Verilog/copy_module.pl \
      src/comp/update-build-version.sh \
      src/comp/update-build-system.sh \
      src/comp/wrapper.sh

    substituteInPlace src/comp/Makefile \
      --replace-fail 'install-bsc install-bluetcl' 'install-bsc install-bluetcl $(UTILEXES) $(SHOWRULESEXES) install-utils install-showrules'
  '';

  preBuild = ''
    # Allow running bsc to bootstrap
    export LD_LIBRARY_PATH=$PWD/inst/lib/SAT

    # Use more cores for GHC building, but not too many to avoid heap overflow
    if [[ $NIX_BUILD_CORES -gt 8 ]] ; then export GHCJOBS=8; else export GHCJOBS=$NIX_BUILD_CORES; fi
  '';

  buildInputs = yices.buildInputs ++ [
    fontconfig
    libX11
    tcl
    tk
    which
    xorg.libXft
    zlib
  ];

  nativeBuildInputs = [
    automake
    autoconf
    bison
    flex
    ghcWithPackages
    gperf
    perl
    pkg-config
    tcl
    makeBinaryWrapper
  ];

  env.NIX_CFLAGS_COMPILE = toString (
    lib.optionals stdenv.cc.isClang [
      "-Wno-error"
    ]
  );

  makeFlags = [
    "NO_DEPS_CHECKS=1"
    "NOGIT=1"
    "LDCONFIG=ldconfig"
    "STP_STUB=1"
    "install-src"
  ];

  installPhase = ''
    mkdir -p $out
    mv inst/bin $out
    mv inst/lib $out
  '';

  postFixup = ''
    wrapProgram $out/bin/core/bsc \
      --prefix PATH : ${lib.makeBinPath [ targetPackages.stdenv.cc ]}
  '';

  doCheck = true;
  checkTarget = "check-smoke";

  nativeCheckInputs = [
    gmp.static
    iverilog
  ];

  installCheckPhase = ''
    output="$($out/bin/bsc 2>&1 || true)"
    echo "$output" | grep -q "to get help"
  '';

  meta = {
    description = "Bluespec Compiler with GAA JSON export patches";
    homepage = "https://github.com/B-Lang-org/bsc";
    license = lib.licenses.bsd3;
    platforms = [ "x86_64-linux" "aarch64-linux" ];
    mainProgram = "bsc";
  };
}
