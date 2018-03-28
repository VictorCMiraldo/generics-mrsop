{ nixpkgs ? import <nixpkgs> {}, compiler ? "ghcHEAD", doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, base, containers, generics-sop, mtl, stdenv
      , template-haskell
      }:
      mkDerivation {
        pname = "generics-mrsop";
        version = "1.0.0.0";
        src = ./.;
        libraryHaskellDepends = [
          base containers generics-sop mtl template-haskell
        ];
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  variant = if doBenchmark then pkgs.haskell.lib.doBenchmark else pkgs.lib.id;

  drv = variant (haskellPackages.callPackage f {});

in

  if pkgs.lib.inNixShell then drv.env else drv
