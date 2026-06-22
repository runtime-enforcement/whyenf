import os
import shutil

from evaluation import run_experiments, merge_summary_dfs

# Acceleration sweep used for every tool on the fun benchmark.
ACCELERATIONS = [1e5, 2e5, 4e5, 8e5, 1.6e6, 3.2e6, 6.4e6, 1.28e7, 2.56e7, 5.12e7]
TIME_UNIT     = 24 * 3600
N             = 1   # iterations per (formula, log, acceleration)
SMOKE_TEST    = False
BINARY_SEARCH = True  # binary-search the fastest real-time acceleration instead of sweeping all


def have(exe: str) -> bool:
    """An executable is usable if the (possibly symlinked) path resolves."""
    return os.path.exists(exe) or shutil.which(exe) is not None


# Tools to evaluate. Each reads the formulae in benchmarks/gdpr/<option>/formulae/
# (enfflash, enfguard and whyenf all share the same MFOTL set via symlink;
# enfpoly only supports the subset it can enforce: consent and lawfulness).
#   * enfflash : our tool (symlink -> repo bin/enfguard.exe, execs Rust enfflash).
#   * enfguard : the old enfguard (symlink -> ~/Tools/enfguard/bin/enfguard.exe).
#   * whyenf   : the WhyEnf enforcer (symlink -> ~/Tools/whyenf/bin/whyenf.exe).
#   * enfpoly  : the Enfpoly fork of MonPoly (symlink -> ~/Tools/monpoly/monpoly).
TOOLS = [
    ('enfflash', './enfflash.exe'),
    ('enfguard', './enfguard.exe'),
]

results = {}

for option, exe in TOOLS:
    if not have(exe):
        print(f"[skip] {option}: executable {exe} not found.")
        continue
    result = run_experiments(
        option        = option,
        benchmark     = 'fun',
        exe           = exe,
        accelerations = ACCELERATIONS,
        n             = N,
        time_unit     = TIME_UNIT,
        func          = True,
        only_graph    = False,
        to            = 60,
        smoke_test    = SMOKE_TEST,
        binary_search = BINARY_SEARCH,
    )
    results[option] = result

print(merge_summary_dfs(results))