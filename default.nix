{
  pkgs ? import <nixpkgs> { },
}:
let
  inherit (pkgs) lib buildNimPackage nim;
in
buildNimPackage {
  pname = "preserves-nim";
  version = "unstable";

  lockFile = ./lock.json;

  src = if lib.inNixShell then null else lib.cleanSource ./.;

  nimFlags = [ "--path:${nim.passthru.nim}/nim" ];
  # Path to the compiler/ast library.

  postInstall = ''
    pushd $out/bin
    for link in preserves_decode preserves_from_json preserves_to_json;
      do ln -s  preserves_encode $link
    done
    mv preserves_schemac preserves-schemac
    popd
  '';
}
