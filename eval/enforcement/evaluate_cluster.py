import os
import shutil

from evaluation import run_experiments, merge_summary_dfs

ACCELERATIONS = [1, 2, 4, 8, 16, 32, 64, 128, 256]
TIME_UNIT     = 1
N             = 3   # iterations per (formula, log, acceleration)
SMOKE_TEST    = False
BINARY_SEARCH = True  # binary-search the fastest real-time acceleration instead of sweeping all


def have(exe: str) -> bool:
    """An executable is usable if the (possibly symlinked) path resolves."""
    return os.path.exists(exe) or shutil.which(exe) is not None


# Tools to evaluate. Each reads the formulae in benchmarks/cluster/<option>/formulae/
# (enfflash and enfguard share the same MFOTL set via symlink -> lifeboat).
#   * enfflash : our tool (symlink -> repo bin/enfflash.exe, execs Rust enfflash).
#   * enfguard : the old enfguard (symlink -> ~/Tools/enfguard/bin/enfguard.exe).
TOOLS = [
    ('enfflash', './enfflash.exe'),
    #('enfguard', './enfguard.exe'),
]

results = {}

for option, exe in TOOLS:
    if not have(exe):
        print(f"[skip] {option}: executable {exe} not found.")
        continue
    result = run_experiments(
        option        = option,
        benchmark     = 'cluster',
        exe           = exe,
        n             = N,
        time_unit     = TIME_UNIT,
        func          = True,
        only_graph    = False,
        to            = 60,
        smoke_test    = SMOKE_TEST,
    )
    results[option] = result

print(merge_summary_dfs(results))

