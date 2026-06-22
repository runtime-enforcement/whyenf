import os
import shutil

from evaluation import run_experiments, merge_summary_dfs

ACCELERATIONS = [1, 2, 4, 8, 16, 32, 64, 128, 256]
TIME_UNIT     = 1
N             = 1   # iterations per (formula, log, acceleration)
SMOKE_TEST    = False
BINARY_SEARCH = True  # binary-search the fastest real-time acceleration instead of sweeping all


def have(exe: str) -> bool:
    """An executable is usable if the (possibly symlinked) path resolves."""
    return os.path.exists(exe) or shutil.which(exe) is not None


# Tools to evaluate. Each reads the formulae in benchmarks/ic/<option>/formulae/
# (enfflash and enfguard share the same MFOTL set via symlink enfflash -> enfguard).
#   * enfflash : our tool (symlink -> repo bin/enfguard.exe, execs Rust enfflash).
#   * monpoly  : MonPoly monitor (symlink -> ~/Tools/monpoly/monpoly).
#   * enfguard : the old enfguard (symlink -> ~/Tools/enfguard/bin/enfguard.exe).
TOOLS = [
    ('enfflash', './enfflash.exe'),
    ('monpoly',  './monpoly.exe'),
    ('enfguard', './enfguard.exe'),
]

results = {}

for option, exe in TOOLS:
    if not have(exe):
        print(f"[skip] {option}: executable {exe} not found.")
        continue
    result = run_experiments(
        option        = option,
        benchmark     = 'ic',
        exe           = exe,
        accelerations = ACCELERATIONS,
        n             = N,
        time_unit     = TIME_UNIT,
        only_graph    = False,
        to            = 600,
        smoke_test    = SMOKE_TEST,
        binary_search = BINARY_SEARCH,
    )
    results[option] = result

print(merge_summary_dfs(results))
