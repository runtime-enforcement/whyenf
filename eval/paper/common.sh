# Shared helpers for the paper's evaluation scripts (sourced, not run).

# Repositories and executables; override from the environment if needed.
# Everything defaults to this repository; proactive-enforcement-library (PEL)
# is vendored in eval/vendor/pel (see eval/paper/docker/vendor.sh).
WHYENF="${WHYENF:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"
PEL="${PEL:-$WHYENF/eval/vendor/pel}"
ENFFLASH="${ENFFLASH:-$WHYENF/_build/default/bin/enfflash.exe}"
# Where the tables (tables/*.tex) and figures (figures/*.pdf) are written; set
# PAPER to the paper repository to write them where main.tex \inputs them.
PAPER="${PAPER:-$WHYENF/eval/paper/output}"
TABLES="${TABLES:-$PAPER/tables}"
export WHYENF PEL PAPER

# Split a comma-separated list, expanding "all" to the given defaults.
#   expand_list "$arg" "a,b,c"
expand_list() {
    local arg="$1" all="$2"
    [[ "$arg" == all ]] && arg="$all"
    tr ',' ' ' <<<"$arg"
}

# Membership test: in_list x "a b c"
in_list() {
    local x="$1"; shift
    for y in $1; do [[ "$x" == "$y" ]] && return 0; done
    return 1
}

# Pin every CPU to the `performance` governor for the rest of the script and
# restore the previous governor on exit.  Refuses to continue otherwise:
# measurements are never taken under `powersave`.  If every CPU is already on
# `performance` (e.g. pinned on the host before starting the Docker container),
# nothing needs to be changed.  GOVERNOR_CHECK=0 skips the check (machines
# without cpufreq, such as most VMs); the measurements are then less reliable.
governors_ok() {
    local g
    g="$(cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor 2>/dev/null)" || return 1
    [[ -n "$g" ]] && ! grep -qv '^performance$' <<<"$g"
}
pin_performance() {
    if [[ "${GOVERNOR_CHECK:-1}" == 0 ]]; then
        echo "WARNING: GOVERNOR_CHECK=0, the CPU governor is not checked." >&2
        return 0
    fi
    if governors_ok; then
        echo "CPU governor: performance"
        return 0
    fi
    local orig
    orig="$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || true)"
    if [[ -z "$orig" ]] || ! command -v cpupower >/dev/null 2>&1; then
        echo "ERROR: cannot read or set the CPU governor (cpufreq/cpupower missing); refusing to run." >&2
        echo "       Pin it to performance first, or set GOVERNOR_CHECK=0 to skip the check." >&2
        exit 1
    fi
    sudo cpupower frequency-set -g performance >/dev/null || {
        echo "ERROR: could not set the CPU governor to performance; refusing to run." >&2
        exit 1
    }
    # shellcheck disable=SC2064
    trap "echo 'Restoring CPU governor -> $orig'; sudo cpupower frequency-set -g '$orig' >/dev/null 2>&1 || true" EXIT
    if ! governors_ok; then
        echo "ERROR: some CPUs are not on the performance governor; refusing to run." >&2
        exit 1
    fi
    echo "CPU governor: performance"
}
