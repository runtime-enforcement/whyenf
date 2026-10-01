# Shared helpers for the paper's evaluation scripts (sourced, not run).

# Repositories and executables; override from the environment if needed.
WHYENF="${WHYENF:-$HOME/Git/whyenf}"
PEL="${PEL:-$HOME/Git/proactive-enforcement-library}"
ENFFLASH="${ENFFLASH:-$WHYENF/_build/default/bin/enfflash.exe}"
# The paper repository; the scripts write its tables/*.tex (\input by main.tex).
PAPER="${PAPER:-$HOME/Overleaf/Enfflash}"
TABLES="${TABLES:-$PAPER/tables}"

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
# measurements are never taken under `powersave`.
pin_performance() {
    local orig
    orig="$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || true)"
    if [[ -z "$orig" ]] || ! command -v cpupower >/dev/null 2>&1; then
        echo "ERROR: cannot read or set the CPU governor (cpufreq/cpupower missing); refusing to run." >&2
        exit 1
    fi
    if [[ "$orig" != performance ]]; then
        sudo cpupower frequency-set -g performance >/dev/null || {
            echo "ERROR: could not set the CPU governor to performance; refusing to run." >&2
            exit 1
        }
        # shellcheck disable=SC2064
        trap "echo 'Restoring CPU governor -> $orig'; sudo cpupower frequency-set -g '$orig' >/dev/null 2>&1 || true" EXIT
    fi
    if grep -qv '^performance$' /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor; then
        echo "ERROR: some CPUs are not on the performance governor; refusing to run." >&2
        exit 1
    fi
    echo "CPU governor: performance"
}
