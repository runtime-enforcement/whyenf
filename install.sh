#!/usr/bin/env bash
# Build EnfFlash and install what it needs: Rust (rustup), OCaml (opam), and the
# OCaml libraries listed in enfflash.opam.  Safe to run again: steps that are
# already done are skipped.
#
# Usage: ./install.sh
#
# OPAM_SWITCH=<name> builds in that opam switch instead of the current one (or,
# if there is none, a new switch "enfflash" with OCaml 4.13.1).
set -euo pipefail
cd "$(dirname "$0")"

step() { printf '\n\033[1m==> %s\033[0m\n' "$*"; }
die()  { printf '\033[31merror:\033[0m %s\n' "$*" >&2; exit 1; }

# ── Rust ──────────────────────────────────────────────────────────────────
step "Rust"
[[ -f "$HOME/.cargo/env" ]] && source "$HOME/.cargo/env"
if ! command -v cargo >/dev/null; then
    echo "Installing Rust with rustup (https://rustup.rs) ..."
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal
    source "$HOME/.cargo/env"
fi
cargo --version

# ── opam ──────────────────────────────────────────────────────────────────
step "opam"
if ! command -v opam >/dev/null; then
    if command -v apt-get >/dev/null; then
        sudo apt-get update && sudo apt-get install -y opam
    elif command -v brew >/dev/null; then
        brew install opam
    else
        die "please install opam (https://opam.ocaml.org/doc/Install.html) and run this script again"
    fi
fi
if ! opam switch list >/dev/null 2>&1; then
    opam init -y --bare
fi
opam --version

# ── OCaml switch ──────────────────────────────────────────────────────────
step "OCaml"
SWITCH="${OPAM_SWITCH:-$(opam switch show 2>/dev/null || true)}"
if [[ -z "$SWITCH" ]]; then
    SWITCH=enfflash
fi
if ! opam switch list --short 2>/dev/null | grep -qx "$SWITCH"; then
    echo "Creating the opam switch $SWITCH (OCaml 4.13.1); this takes a few minutes ..."
    opam switch create "$SWITCH" 4.13.1 -y
fi
eval "$(opam env --switch="$SWITCH" --set-switch)"
echo "switch $SWITCH, $(ocaml -version)"

# ── OCaml libraries ───────────────────────────────────────────────────────
step "OCaml libraries (the first time, building z3 takes a while)"
# opam also installs the system packages they need (e.g. GMP), asking for sudo.
opam install . --deps-only -y

# ── Build ─────────────────────────────────────────────────────────────────
step "Building EnfFlash"
make

step "Done"
cat <<EOF
EnfFlash is built: bin/enfflash.exe

Try it:
  ./bin/enfflash.exe -sig examples/quickstart/consent.sig \\
                     -formula examples/quickstart/consent.mfotl \\
                     -log examples/quickstart/consent.log

In a new shell, run  eval \$(opam env --switch=$SWITCH)  before rebuilding with  make.
EOF
