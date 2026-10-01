#!/usr/bin/env bash
# Rerun every measurement of the given tools, in all four tables, and regenerate
# the tables and figures.
#
# Usage: eval/paper/rerun.sh --tools TOOLS [--tables 1,2,3,4] [--dry-run]
#
#   --tools    tools to rerun, comma-separated, or "all"; each table reruns the
#              ones it measures, and the others are skipped:
#                table 1: enfflash,enfpoly,enfguard,dogwood,monpoly
#                table 2: enfflash,baseline
#                table 3: enfflash,dogwood,cedar
#                table 4: enfflash,enfguard,dogwood
#   --tables   restrict to these tables                           (default: 1,2,3,4)
#   --dry-run  only print the commands
#
# The tables run in order with their default parameters; a table that fails is
# reported at the end and does not stop the others.  Each table's output is in
# eval/paper/logs/rerun_<date>/tableN.log.
# Examples: eval/paper/rerun.sh --tools dogwood
#           eval/paper/rerun.sh --tools enfflash,dogwood --tables 3,4
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
source "$HERE/common.sh"

TOOLS_1=enfflash,enfpoly,enfguard,dogwood,monpoly
TOOLS_2=enfflash,baseline
TOOLS_3=enfflash,dogwood,cedar
TOOLS_4=enfflash,enfguard,dogwood
ALL="$(tr ',' '\n' <<<"$TOOLS_1,$TOOLS_2,$TOOLS_3,$TOOLS_4" | awk '!seen[$0]++' | paste -sd,)"

TOOLS="" TABLES="1 2 3 4" DRY=0
while [[ $# -gt 0 ]]; do
    case "$1" in
        --tools)   TOOLS="$(expand_list "$2" "$ALL")"; shift 2 ;;
        --tables)  TABLES="$(tr ',' ' ' <<<"$2")"; shift 2 ;;
        --dry-run) DRY=1; shift ;;
        *) sed -n '2,21p' "$0"; exit 1 ;;
    esac
done
[[ -n "$TOOLS" ]] || { sed -n '2,21p' "$0"; exit 1; }
for t in $TOOLS; do in_list "$t" "$(tr ',' ' ' <<<"$ALL")" || { echo "unknown tool $t"; exit 1; }; done
for n in $TABLES; do in_list "$n" "1 2 3 4" || { echo "unknown table $n"; exit 1; }; done

# The commands: for each table, the requested tools it measures.
plan=()
for n in $TABLES; do
    var="TOOLS_$n"; sel=""
    for t in $TOOLS; do
        in_list "$t" "$(tr ',' ' ' <<<"${!var}")" && sel="${sel:+$sel,}$t"
    done
    [[ -n "$sel" ]] && plan+=("$n:$sel")
done
[[ ${#plan[@]} -gt 0 ]] || { echo "no selected table measures these tools"; exit 1; }
for p in "${plan[@]}"; do echo "table${p%%:*}.sh --tools ${p#*:}"; done
[[ "$DRY" == 1 ]] && exit 0

# Pin the governor once, so that sudo asks at most once; the table scripts
# then find it already on performance.
pin_performance
LOGS="$HERE/logs/rerun_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$LOGS"
failed=()
for p in "${plan[@]}"; do
    n="${p%%:*}" sel="${p#*:}"
    echo "── $(date +%T) table $n: $sel  (log: $LOGS/table$n.log)"
    if "$HERE/table$n.sh" --tools "$sel" > "$LOGS/table$n.log" 2>&1; then
        echo "   $(date +%T) done"
    else
        echo "   $(date +%T) FAILED (exit $?), see the log"
        failed+=("$n")
    fi
done
if [[ ${#failed[@]} -gt 0 ]]; then
    echo "Failed tables: ${failed[*]}"
    exit 1
fi
echo "All tables rerun; tables and figures regenerated in $PAPER."
