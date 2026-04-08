#!/usr/bin/env python3
"""
Benchmark: enfflash (Rust engine) vs old enfguard (OCaml-only enforcement).

Steps:
  1. Generate a ~100-timepoint GDPR-compliant log
  2. Build & run current enfguard with -run (compiles .ef, execs enfflash)
  3. Switch to branch new_temp, build & run old OCaml enfguard
  4. Report timing comparison

Usage:
  python3 benchmark/bench.py [--timepoints N]
"""

import argparse
import os
import random
import shutil
import subprocess
import sys
import tempfile
import time

# ── paths ───────────────────────────────────────────────────────────────────
WHYENF   = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GDPR_DIR = os.path.join(os.path.dirname(WHYENF), "Lex", "example", "GDPR")

FORMULA  = os.path.join(GDPR_DIR, "minitwit_gdpr.mfotl")
SIG      = os.path.join(GDPR_DIR, "minitwit_gdpr.sig")
FUNC     = os.path.join(GDPR_DIR, "gdpr.py")

NEW_BRANCH = "enfflash"      # current branch with enfflash support
OLD_BRANCH = "new_temp"      # branch with old OCaml-only enforcement


# ── log generation ──────────────────────────────────────────────────────────
# Event signatures (from minitwit_gdpr.sig):
#   Collect(activity, data, owner, purpose)
#   PersonalData(d, ds)
#   Consent(user, purpose)-
#   IsCompatibleWithPurpose(a, p)
#   Read(id, owner, activity, purpose, user)
#   Write(id, owner, activity, purpose, user)
#   Send(entity, data)
#   DailyErasureReview(data)+

PURPOSES  = ["service", "statistics", "marketing", "analytics"]
ENTITIES  = ['"Analytics, Inc."', '"Research Corp."', '"AdTech Ltd."']


def generate_log(n_timepoints: int, path: str) -> None:
    """Generate a GDPR-compliant log with *n_timepoints* time-points."""
    random.seed(42)

    users       = list(range(1, 6))        # user ids 1..5
    data_items  = list(range(1, 4))        # data ids 1..3
    activities  = list(range(1, 4))        # activity ids 1..3

    # Keep track of which (user, purpose) pairs have consent so the log
    # stays compliant (Consent must precede usage for that purpose).
    consented: set[tuple[int, str]] = set()
    collected: set[tuple[int, int, str]] = set()   # (activity, data, purpose)

    lines: list[str] = []

    for tp in range(1, n_timepoints + 1):
        events: list[str] = []

        # --- Phase 1: consent & collection (first ~30 %) ---
        if tp <= max(1, n_timepoints // 3):
            user    = random.choice(users)
            data    = random.choice(data_items)
            act     = random.choice(activities)
            purpose = random.choice(PURPOSES)

            # Ensure consent
            if (user, purpose) not in consented:
                events.append(f'Consent({user},"{purpose}")')
                consented.add((user, purpose))

            events.append(f"PersonalData({data},{user})")
            events.append(f'IsCompatibleWithPurpose({act},"{purpose}")')

            if (act, data, purpose) not in collected:
                events.append(f'Collect({act},{data},{user},"{purpose}")')
                collected.add((act, data, purpose))

        # --- Phase 2: reads / writes (middle ~50 %) ---
        elif tp <= max(2, 4 * n_timepoints // 5):
            kind = random.choice(["read", "write", "read", "read"])
            user    = random.choice(users)
            data    = random.choice(data_items)
            act     = random.choice(activities)
            purpose = random.choice(PURPOSES)

            # Make sure we have consent for this user+purpose
            if (user, purpose) not in consented:
                events.append(f'Consent({user},"{purpose}")')
                consented.add((user, purpose))

            events.append(f"PersonalData({data},{user})")
            events.append(f'IsCompatibleWithPurpose({act},"{purpose}")')

            if kind == "read":
                events.append(f'Read({act},{user},{data},"{purpose}",{user})')
            else:
                events.append(f'Write({act},{user},{data},"{purpose}",{user})')

        # --- Phase 3: sends & erasure reviews (last ~20 %) ---
        else:
            coin = random.random()
            if coin < 0.5:
                entity = random.choice(ENTITIES)
                data   = random.choice(data_items)
                events.append(f"Send({entity},{data})")
            else:
                data = random.choice(data_items)
                events.append(f"DailyErasureReview({data})")

        lines.append(f"@{tp} {' '.join(events)};")

    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")

    print(f"  Generated {n_timepoints}-timepoint log → {path}")


# ── helpers ─────────────────────────────────────────────────────────────────
def run_cmd(cmd: list[str], cwd: str | None = None,
            timeout: int = 300) -> tuple[float, str, str]:
    """Run *cmd*, return (elapsed_seconds, stdout, stderr)."""
    print(f"  $ {' '.join(cmd)}")
    start = time.perf_counter()
    proc = subprocess.run(cmd, capture_output=True, text=True,
                          cwd=cwd, timeout=timeout)
    elapsed = time.perf_counter() - start
    return elapsed, proc.stdout, proc.stderr


def git_current_branch(repo: str) -> str:
    out = subprocess.check_output(
        ["git", "branch", "--show-current"], cwd=repo, text=True)
    return out.strip()


def git_stash_if_dirty(repo: str) -> bool:
    """Stash only tracked changes (avoid permission errors on files like perf.data)."""
    status = subprocess.check_output(
        ["git", "status", "--porcelain"], cwd=repo, text=True).strip()
    # Only consider tracked (modified/staged) files, ignore untracked lines ("?? …")
    tracked_dirty = [l for l in status.splitlines() if not l.startswith("??")]
    if tracked_dirty:
        subprocess.check_call(["git", "stash"], cwd=repo)
        return True
    return False


def git_checkout(repo: str, branch: str) -> None:
    subprocess.check_call(["git", "checkout", branch], cwd=repo,
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def build_enfguard(repo: str) -> str:
    """Build enfguard with dune, return path to the binary."""
    print("  Building enfguard …")
    subprocess.check_call(["dune", "build"], cwd=repo,
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    # dune exec resolves to the correct binary
    return "dune"


# ── main ────────────────────────────────────────────────────────────────────
def main() -> None:
    parser = argparse.ArgumentParser(description="Benchmark enfflash vs old enfguard")
    parser.add_argument("--timepoints", "-n", type=int, default=100,
                        help="Number of time-points in the generated log (default: 100)")
    args = parser.parse_args()

    for p, label in [(FORMULA, "formula"), (SIG, "sig"), (FUNC, "func")]:
        if not os.path.isfile(p):
            sys.exit(f"Error: {label} file not found: {p}")

    original_branch = git_current_branch(WHYENF)
    stashed = False

    # Temporary log file
    tmp_dir = tempfile.mkdtemp(prefix="enfbench_")
    log_path = os.path.join(tmp_dir, "bench.log")

    print(f"\n{'=' * 60}")
    print(f" Benchmark: enfflash vs old enfguard")
    print(f" Time-points: {args.timepoints}")
    print(f"{'=' * 60}\n")

    try:
        # ── 1. Generate log ─────────────────────────────────────────
        print("[1/5] Generating log …")
        generate_log(args.timepoints, log_path)

        # ── 2. Build enfflash branch ────────────────────────────────
        print(f"\n[2/5] Building enfguard on branch '{NEW_BRANCH}' …")
        if git_current_branch(WHYENF) != NEW_BRANCH:
            stashed = git_stash_if_dirty(WHYENF)
            git_checkout(WHYENF, NEW_BRANCH)
        build_enfguard(WHYENF)

        # Also make sure the Rust enfflash binary is built
        enfflash_bin = os.path.join(WHYENF, "enfflash", "target", "release", "enfflash")
        if not os.path.isfile(enfflash_bin):
            print("  Building enfflash (Rust) …")
            subprocess.check_call(["cargo", "build", "--release"],
                                  cwd=os.path.join(WHYENF, "enfflash"),
                                  stdout=subprocess.DEVNULL,
                                  stderr=subprocess.DEVNULL)

        # ── 3. Run enfflash ─────────────────────────────────────────
        print(f"\n[3/5] Running enfguard + enfflash (Rust engine) …")
        enfflash_cmd = [
            "dune", "exec", "bin/enfguard.bc", "--",
            "-run",
            "-sig", SIG,
            "-formula", FORMULA,
            "-func", FUNC,
            "-log", log_path,
        ]
        enfflash_time, ef_stdout, ef_stderr = run_cmd(enfflash_cmd, cwd=WHYENF)
        print(f"  ✓ Finished in {enfflash_time:.3f}s")

        # ── 4. Switch to old branch & build ─────────────────────────
        print(f"\n[4/5] Switching to branch '{OLD_BRANCH}' and building …")
        stashed = git_stash_if_dirty(WHYENF) or stashed
        git_checkout(WHYENF, OLD_BRANCH)
        build_enfguard(WHYENF)

        # ── 5. Run old enfguard ─────────────────────────────────────
        print(f"\n[5/5] Running old enfguard (OCaml-only enforcement) …")
        old_cmd = [
            "dune", "exec", "bin/enfguard.bc", "--",
            "-sig", SIG,
            "-formula", FORMULA,
            "-func", FUNC,
            "-log", log_path,
        ]
        old_time, old_stdout, old_stderr = run_cmd(old_cmd, cwd=WHYENF)
        print(f"  ✓ Finished in {old_time:.3f}s")

        # ── Report ──────────────────────────────────────────────────
        print(f"\n{'=' * 60}")
        print(f" RESULTS  ({args.timepoints} time-points)")
        print(f"{'=' * 60}")
        print(f"  enfflash (Rust engine) : {enfflash_time:8.3f}s")
        print(f"  old enfguard (OCaml)   : {old_time:8.3f}s")
        if old_time > 0:
            speedup = old_time / enfflash_time
            print(f"  speed-up               : {speedup:8.2f}×")
        print(f"{'=' * 60}\n")

        # Optionally dump outputs for diff
        ef_out_path  = os.path.join(tmp_dir, "enfflash.out")
        old_out_path = os.path.join(tmp_dir, "old.out")
        with open(ef_out_path, "w")  as f: f.write(ef_stdout)
        with open(old_out_path, "w") as f: f.write(old_stdout)
        print(f"  Outputs saved to {tmp_dir}/")
        if ef_stderr.strip():
            print(f"  [enfflash stderr]: {ef_stderr[:500]}")
        if old_stderr.strip():
            print(f"  [old enfguard stderr]: {old_stderr[:500]}")

    finally:
        # ── Restore original branch ────────────────────────────────
        print(f"\nRestoring branch '{original_branch}' …")
        git_checkout(WHYENF, original_branch)
        if stashed:
            subprocess.call(["git", "stash", "pop"], cwd=WHYENF,
                            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        print("Done.")


if __name__ == "__main__":
    main()
