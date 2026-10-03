#!/usr/bin/env bash
# Build every tool the evaluation measures and link it where the scripts expect
# it (eval/enforcement/<tool>.exe).  Used by the Docker image; works on any
# machine with the OCaml switch (see install.sh) and Rust toolchain installed.
#
# Usage: eval/paper/build_tools.sh [--force-links]
#
#   EnfFlash  OCaml front end (dune) + Rust engine (enfflash/)
#   EnfGuard  eval/vendor/enfguard (submodule)           -> eval/enforcement/enfguard.exe
#   MonPoly   eval/vendor/monpoly (submodule, enfpoly;  -> eval/enforcement/{monpoly,enfpoly}.exe
#             Enfpoly, in -enforce mode)
#   Dogwood   eval/enforcement/dogwood (log replayer)  -> eval/enforcement/dogwood.exe
#             and the Python binding of the EventManager baseline (Table 3)
#
# An existing working link in eval/enforcement/ is kept unless --force-links.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
source "$HERE/common.sh"
FORCE=0
[[ "${1:-}" == --force-links ]] && FORCE=1
ENF="$WHYENF/eval/enforcement"
VENDOR="$WHYENF/eval/vendor"

for m in enfguard monpoly; do
    [[ -f "$VENDOR/$m/dune-project" ]] || {
        echo "ERROR: eval/vendor/$m is empty: run 'git submodule update --init'." >&2; exit 1; }
done

step() { printf '\n==> %s\n' "$*"; }
link() {  # link <target relative to eval/enforcement> <name>
    if [[ "$FORCE" == 1 || ! -e "$ENF/$2" ]]; then
        ln -sfn "$1" "$ENF/$2"
    fi
    echo "  $2 -> $(readlink "$ENF/$2")"
}

step "EnfFlash"
(cd "$WHYENF" && dune build bin/enfflash.exe)
(cd "$WHYENF/enfflash" && cargo build --release)
link ../../_build/default/bin/enfflash.exe enfflash.exe

step "EnfGuard"
(cd "$VENDOR/enfguard" && dune build --root . bin/enfguard.exe)
link ../vendor/enfguard/_build/default/bin/enfguard.exe enfguard.exe

step "MonPoly / Enfpoly"
(cd "$VENDOR/monpoly" && dune build --root . src/main.exe)
link ../vendor/monpoly/monpoly monpoly.exe
link ../vendor/monpoly/monpoly enfpoly.exe

step "Dogwood"
(cd "$ENF/dogwood" && cargo build --release)
link dogwood/target/release/dogwood-enforce dogwood.exe
make -C "$PEL/event_platform/benchmark/privacy_testsuite/baseline/event_platform_dogwood" binding

step "Done"
