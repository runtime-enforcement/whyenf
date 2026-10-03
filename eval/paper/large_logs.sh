#!/usr/bin/env bash
# The two benchmark logs of Table 1 that exceed GitHub's file size limit are
# committed compressed and split into parts of at most 45 MB, in
# eval/enforcement/benchmarks/large/.  This script recreates them in place.
#
# Usage: eval/paper/large_logs.sh [restore]   recreate the logs from the parts (default)
#        eval/paper/large_logs.sh pack        maintainers: rebuild the parts from the logs
#
# The other tools' copies of these logs are committed symlinks to them.
# Checksums: eval/paper/docker/data.sha256.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
B="$ROOT/eval/enforcement/benchmarks"
PARTS="$B/large"
SUMS="$ROOT/eval/paper/docker/data.sha256"
# name of the parts : the log, relative to eval/enforcement/benchmarks
LOGS=(
    "ic:ic/enfguard/logs/nightly_default_subnet_query_workload_long_duration_test__nightly_default_subnet_query_workload_long_duration_test-2982312912.log"
    "nokia:nokia/enfguard/logs/ldcc_short.log"
)

case "${1:-restore}" in
    restore)
        for e in "${LOGS[@]}"; do
            name="${e%%:*}" log="$B/${e#*:}"
            if [[ -f "$log" ]] && grep -F "${log#"$ROOT"/}" "$SUMS" | (cd "$ROOT" && sha256sum -c --quiet --status); then
                echo "ok       ${log#"$ROOT"/}"
                continue
            fi
            echo "restore  ${log#"$ROOT"/}"
            mkdir -p "$(dirname "$log")"
            cat "$PARTS/$name.log.xz.part-"* | xz -d -T0 > "$log.tmp"
            mv "$log.tmp" "$log"
        done
        (cd "$ROOT" && sha256sum -c "$SUMS")
        ;;
    pack)
        mkdir -p "$PARTS"
        for e in "${LOGS[@]}"; do
            name="${e%%:*}" log="$B/${e#*:}"
            rm -f "$PARTS/$name.log.xz.part-"*
            xz -6 -T0 -c "$log" | split -b 45M -d -a 2 - "$PARTS/$name.log.xz.part-"
            ls -la "$PARTS/$name.log.xz.part-"*
        done
        ;;
    *) sed -n '2,11p' "$0"; exit 1 ;;
esac
