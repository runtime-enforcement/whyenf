# Evaluation: reproducing the measurements

This document describes how to reproduce the empirical evaluation in `eval/enforcement/`.

Benchmarks covered: **gdpr**, **fun**, **cluster**, **agg**, **ic**, **nokia**.

Each benchmark compares a subset of the following tools:

| Symlink | Tool | Benchmark(s) |
|---------|------|-------------|
| `enfflash.exe` | Enfflash (this repo) | all |
| `enfguard.exe` | EnfGuard (old enforcer) | gdpr, fun, agg, ic, nokia |
| `monpoly.exe` | MonPoly | gdpr, agg, ic, nokia |
| `enfpoly.exe` | Enfpoly (MonPoly enforcement branch) | gdpr, nokia |
| `whyenf.exe` | WhyEnf | (gdpr, nokia — currently disabled) |

---

## Step 0 — System requirements

- OCaml ≥ 4.13, opam, Rust stable toolchain (for Enfflash)
- Python ≥ 3.8
- ~32 GB RAM recommended; experiments were run on an Intel i5-1135G7 (2.4 GHz), Ubuntu 22.04

---

## Step 1 — Build Enfflash (this repo)

From the repo root:

```bash
# OCaml frontend
opam install dune core_kernel core_unix base zarith menhir \
             zarith_stubs_js dune-build-info qcheck pyml calendar str z3
dune build

# Rust enforcement engine
cargo build --release --manifest-path enfflash/Cargo.toml
```

The `eval/enforcement/enfflash.exe` symlink already points to
`../../_build/default/bin/enfflash.exe` (the OCaml frontend, which execs the
Rust engine automatically).

---

## Step 2 — Install comparison tools

All tools should be installed under `~/Tools/`.  
Each tool needs a symlink in `eval/enforcement/` pointing at its binary.

### MonPoly and Enfpoly

MonPoly and Enfpoly share the same binary (the mode is selected by flags).
Clone the `enfpoly` branch of MonPoly's repository:

```bash
mkdir -p ~/Tools && cd ~/Tools
git clone https://bitbucket.org/jshs/monpoly.git
cd monpoly
git checkout enfpoly          # branch that adds enforcement support
opam install dune zarith
dune build
```

Create a thin wrapper script at `~/Tools/monpoly/monpoly` if not already
present (the build sometimes creates it automatically — check first):

```bash
# Only needed if the file does not already exist
cat > ~/Tools/monpoly/monpoly << 'EOF'
#!/bin/bash
SELF=${BASH_SOURCE[0]}
while [[ -L $SELF ]]; do SELF=$(readlink -- "$SELF"); done
BASE_DIR=$(cd -P -- "$(dirname -- "$SELF")" && pwd -P)
exec "$BASE_DIR/_build/default/src/main.exe" "$@"
EOF
chmod +x ~/Tools/monpoly/monpoly
```

Then create the symlinks:

```bash
cd /path/to/this/repo/eval/enforcement
ln -sf ~/Tools/monpoly/monpoly monpoly.exe
ln -sf ~/Tools/monpoly/monpoly enfpoly.exe
```

### EnfGuard (old enforcer)

```bash
cd ~/Tools
git clone https://github.com/runtime-enforcement/enfguard.git
cd enfguard
opam install dune core_kernel core_unix base zarith menhir \
             zarith_stubs_js dune-build-info qcheck pyml calendar str z3
dune build
```

Create the symlink:

```bash
cd /path/to/this/repo/eval/enforcement
ln -sf ~/Tools/enfguard/bin/enfguard.exe enfguard.exe
```

### WhyEnf

```bash
cd ~/Tools
git clone https://github.com/runtime-enforcement/whyenf.git
cd whyenf
opam install dune core_kernel core_unix base zarith menhir \
             zarith_stubs_js dune-build-info qcheck pyml calendar str z3
dune build
```

Create the symlink:

```bash
cd /path/to/this/repo/eval/enforcement
ln -sf ~/Tools/whyenf/bin/whyenf.exe whyenf.exe
```

---

## Step 3 — Python environment

```bash
cd eval/enforcement
python3 -m venv .env
source .env/bin/activate
pip install -r requirements.txt
```

---

## Step 4 — Run the benchmarks

Each script evaluates one benchmark and prints a summary table.
Run from `eval/enforcement/` with the virtual environment active.

```bash
cd eval/enforcement
source .env/bin/activate

python3 evaluate_gdpr.py
python3 evaluate_fun.py
python3 evaluate_cluster.py
python3 evaluate_agg.py
python3 evaluate_ic.py
python3 evaluate_nokia.py
```

Results (CSV + per-run PNG plots) are written to `outputs/<benchmark>/<tool>/`.

To generate the combined LaTeX comparison table across all benchmarks:

```bash
python3 all_tables.py
```

### Smoke test

Each script has a `SMOKE_TEST = True` flag at the top that restricts the run to
one formula and one log. Set it before running to verify the setup quickly
(takes seconds instead of hours).

### Skipping unavailable tools

If a tool's symlink is missing or broken the script prints `[skip] <tool>:
executable not found` and continues with the remaining tools. You only need the
tools relevant to the benchmarks you want to reproduce.

---

## Indicative runtimes (full run, N=3 iterations)

| Benchmark | Tools | Approx. duration |
|-----------|-------|-----------------|
| gdpr | enfpoly, monpoly, enfguard | 1–3 h |
| fun | enfflash, enfguard | 30–90 min |
| cluster | enfflash | 15–30 min |
| agg | enfflash, enfguard, monpoly | 30–90 min |
| ic | enfflash, monpoly, enfguard | 1–2 h |
| nokia | enfflash, enfpoly, monpoly, enfguard | 1–3 h |
