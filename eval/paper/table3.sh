#!/usr/bin/env bash
# Table 3 (tab:app2): EventManager page latency, EnfFlash (E) vs. Dogwood (D) vs. Cedar (C).
#
# Usage: eval/paper/table3.sh [--tools TOOLS] [--cache on|off] [-o OUT.tex]
#
#   --tools   tools to rerun, comma-separated, or "all": enfflash,dogwood,cedar (default: none)
#   --cache   the enforcers' result cache (EnfFlash and Dogwood), on or off  (default: on)
#   --users   user counts to measure, e.g. 1,10,100   (default: 1,10,100,1000,10000;
#             View events is not measured at 10000: it renders all 100000 events)
#   -o        LaTeX output          (default: $PAPER/tables/tab_app2.tex)
#
# Only the selected tools are rerun; the table is always regenerated from the
# latest run of each tool (eval/vendor/pel/event_platform/
# benchmark/privacy_testsuite/output/event_platform_<policy>_<date>).
# Example: eval/paper/table3.sh --tools enfflash,dogwood --users 1,10,100
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
source "$HERE/common.sh"
export PY="${PY:-/usr/bin/python3.12}"

TOOLS="" CACHE=on OUT="$TABLES/tab_app2.tex"
while [[ $# -gt 0 ]]; do
    case "$1" in
        --tools) TOOLS="$(expand_list "$2" enfflash,dogwood,cedar)"; shift 2 ;;
        --cache) CACHE="$2"; shift 2 ;;
        --users) export EP_USERS="$2"; shift 2 ;;
        -o)      OUT="$2"; shift 2 ;;
        *) sed -n '2,14p' "$0"; exit 1 ;;
    esac
done
for t in $TOOLS; do in_list "$t" "enfflash dogwood cedar" || { echo "unknown tool $t"; exit 1; }; done

EP="$PEL/event_platform"
SUITE="$EP/benchmark/privacy_testsuite"
POLICY_enfflash=mfotl
POLICY_dogwood=dogwood
POLICY_cedar=cedar

if [[ -n "$TOOLS" ]]; then
    in_list enfflash "$TOOLS" && (cd "$WHYENF" && dune build bin/enfflash.exe)
    if in_list dogwood "$TOOLS" && [[ ! -f "$SUITE/baseline/event_platform_dogwood/src/dogwood_py.abi3.so" ]]; then
        make -C "$SUITE/baseline/event_platform_dogwood" binding
    fi
    pin_performance
    prepared=0
    for t in $TOOLS; do
        policy="POLICY_$t"; policy="${!policy}"
        # The database snapshots do not depend on the tool: build them once.
        SKIP_PREPARE=$prepared "$SUITE/run_benchmark.sh" "$policy" "$ENFFLASH" "$CACHE"
        prepared=1
    done
fi

mkdir -p "$(dirname "$OUT")"
nocache=(); [[ "$CACHE" == off ]] && nocache=(--nocache)
cd "$SUITE"
"$PY" make_table.py -d output "${nocache[@]}" -o "$OUT"
# The figure of this table (panel of fig:eval), from the same results.
"$PY" -W ignore "$HERE/figures.py" app2
