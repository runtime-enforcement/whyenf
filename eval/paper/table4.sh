#!/usr/bin/env bash
# Table 4 (tab:app3): security policies of an LLM banking agent (AgentDojo banking suite).
#
# Usage: eval/paper/table4.sh [--tools TOOLS] [--repeat K] [--timeout S] [-o OUT.tex]
#
#   --tools    tools to rerun, comma-separated, or "all": enfflash,enfguard,dogwood (default: none)
#              enfflash: replay the 16 benign + 144 attacked runs under no enforcement,
#                        each policy B1..B10 and their conjunction, recording the event
#                        logs; measure latency on those logs; the long-history run
#              enfguard, dogwood: measure latency on the recorded logs (needs a prior
#                        enfflash run for the logs); Dogwood runs policies/dogwood/*.dw
#   --repeat   repetitions of the suite in the long-history run          (default: 20)
#   --timeout  per-log timeout of the latency measurements, in seconds   (default: 600)
#   -o         LaTeX output          (default: $PAPER/tables/tab_app3.tex)
#
# Only the selected tools are rerun; the table is always regenerated from the
# stored results (eval/agent_banking/results/).
# Example: eval/paper/table4.sh --tools all
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
source "$HERE/common.sh"
PY="${PY:-/usr/bin/python3.12}"

TOOLS="" REPEAT=20 TIMEOUT=600 OUT="$TABLES/tab_app3.tex"
while [[ $# -gt 0 ]]; do
    case "$1" in
        --tools)   TOOLS="$(expand_list "$2" enfflash,enfguard,dogwood)"; shift 2 ;;
        --repeat)  REPEAT="$2"; shift 2 ;;
        --timeout) TIMEOUT="$2"; shift 2 ;;
        -o)        OUT="$2"; shift 2 ;;
        *) sed -n '2,18p' "$0"; exit 1 ;;
    esac
done
for t in $TOOLS; do in_list "$t" "enfflash enfguard dogwood" || { echo "unknown tool $t"; exit 1; }; done

BANK="$WHYENF/eval/agent_banking"
export ENFFLASH
cd "$BANK"

if [[ -n "$TOOLS" ]]; then
    if in_list enfflash "$TOOLS"; then
        # Rebuild EnfFlash (compiler and engine) so the measurements use the current code.
        (cd "$WHYENF" && dune build bin/enfflash.exe)
        (cd "$WHYENF/enfflash" && cargo build --release)
        # AgentDojo, in the case study's own virtual environment.
        if [[ ! -x .venv/bin/python ]]; then
            python3 -m venv .venv
            .venv/bin/pip install -q agentdojo
        fi
    fi
    if in_list dogwood "$TOOLS" && [[ ! -x "$WHYENF/eval/enforcement/dogwood.exe" ]]; then
        (cd "$WHYENF/eval/enforcement/dogwood" && CARGO_TARGET_DIR="$HOME/.cache/dogwood-target" cargo build --release)
        ln -sf "$HOME/.cache/dogwood-target/release/dogwood-enforce" "$WHYENF/eval/enforcement/dogwood.exe"
    fi
    pin_performance
    "$PY" make_all_dogwood.py
    if in_list enfflash "$TOOLS"; then
        "$PY" make_all.py
        ./check_policies.sh
        mkdir -p results/logs results/scaling
        for p in none b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 all; do
            if [[ "$p" == none ]]; then
                .venv/bin/python replay.py --policy none
            else
                REPLAY_LOG="results/logs/$p.log" .venv/bin/python replay.py --policy "$p"
            fi
        done
        .venv/bin/python replay.py --policy all --repeat "$REPEAT" --out results/scaling
    fi
    offline=""
    for t in $TOOLS; do offline="${offline:+$offline,}$t"; done
    [[ -f results/logs/all.log ]] || { echo "no recorded logs: run --tools enfflash first" >&2; exit 1; }
    "$PY" compare.py --tools "$offline" --timeout "$TIMEOUT"
fi

mkdir -p "$(dirname "$OUT")"
"$PY" report.py
"$PY" report.py --latex -o "$OUT"
# The figure of this table (panel of fig:eval), from the same results.
"$PY" -W ignore "$HERE/figures.py" app3
