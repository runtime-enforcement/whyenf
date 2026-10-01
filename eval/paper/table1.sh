#!/usr/bin/env bash
# Table 1 (tab:micro): EnfGuard benchmark suite.
#
# Usage: eval/paper/table1.sh [--tools TOOLS] [--benchmarks BENCHMARKS] [-n N] [-o OUT.tex]
#
#   --tools       tools to rerun, comma-separated, or "all":
#                 enfflash,enfpoly,enfguard,dogwood,monpoly   (default: none)
#   --benchmarks  benchmarks to rerun: gdpr,fun,cluster,agg,nokia,ic (default: all)
#   -n            repetitions per (formula, log)                      (default: 3)
#   -o            LaTeX output         (default: $PAPER/tables/tab_micro.tex)
#
# Only the selected tools are rerun; the table is always regenerated in full
# from all stored results (eval/enforcement/outputs/<benchmark>/<tool>/).
# Example: eval/paper/table1.sh --tools enfflash,dogwood
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
source "$HERE/common.sh"
PY="${PY:-/usr/bin/python3.12}"
export TABLES

if [[ " $* " == *" --tools "* ]]; then
    # Rebuild Enfflash first so the measurements use the current compiler.
    (cd "$WHYENF" && dune build bin/enfflash.exe)
    pin_performance
fi
"$PY" "$HERE/table1.py" "$@"
# The figure of this table (panel of fig:eval), from the same results.
"$PY" -W ignore "$HERE/figures.py" micro
