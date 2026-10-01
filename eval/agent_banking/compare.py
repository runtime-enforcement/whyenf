"""Replay the recorded event logs (results/logs/<policy>.log, written by
replay.py with REPLAY_LOG) through EnfFlash, EnfGuard and Dogwood, and measure
their latency.

Each time-point is sent followed by the marker `> LATENCY <tp> <ts> <`, which
every tool echoes, with its number of caused and suppressed events, once it has
processed the time-point (the protocol of eval/enforcement/replayer.py).  The
latency of a time-point is the time from sending it to reading the echo.  The
suppression counts of EnfGuard and Dogwood are compared with EnfFlash's, time-
point by time-point, to check that they enforce the same policy.

Dogwood runs the policies of policies/dogwood/<policy>_*.dw; it cannot cause
events, so only the suppression part of B5, B6 and B8 is translated, and B9 is
not.  A run that exceeds the timeout reports how many time-points it processed.

Usage: compare.py [--tools enfflash,enfguard,dogwood] [--policies b1,...] [--timeout S]

Only the selected tools and policies are rerun; results/compare.json keeps the others.
"""

import argparse
import json
import os
import subprocess
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
POL = HERE / "policies"
SIG = POL / "banking.sig"
LOGS = HERE / "results" / "logs"
OUT = HERE / "results" / "compare.json"
# The executables of Table 1 (eval/enforcement/<tool>.exe); ENFFLASH overrides EnfFlash's.
ENF = HERE.parent / "enforcement"
EXE = {
    "enfflash": os.environ.get("ENFFLASH", str(ENF / "enfflash.exe")),
    "enfguard": str(ENF / "enfguard.exe"),
    "dogwood": str(ENF / "dogwood.exe"),
}
POLICIES = ["b1", "b2", "b3", "b4", "b5", "b6", "b7", "b8", "b9", "b10", "all"]


def formula(tool: str, p: str) -> Path | None:
    d, ext = (POL / "dogwood", "dw") if tool == "dogwood" else (POL, "mfotl")
    m = sorted(d.glob(f"{p}_*.{ext}")) or [d / f"{p}.{ext}"]
    return m[0] if m[0].exists() else None


def run(tool: str, p: str, timeout: float) -> dict | None:
    f = formula(tool, p)
    if f is None:
        return None
    lines = [l.rstrip("\n") for l in (LOGS / f"{p}.log").open() if l.startswith("@")]
    proc = subprocess.Popen([EXE[tool], "-sig", str(SIG), "-formula", str(f)],
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.DEVNULL, text=True, bufsize=1)
    timer = threading.Timer(timeout, proc.kill)
    timer.start()
    lat_ns, sup, started = [], [], time.perf_counter()
    try:
        # Start-up (parsing, compiling the policy) is not part of the latency:
        # wait for the echo of a first marker.
        proc.stdin.write("> LATENCY -1 0 <\n")
        proc.stdin.flush()
        while True:
            out = proc.stdout.readline()
            if not out:
                raise BrokenPipeError
            if out.startswith("> LATENCY "):
                break
        for tp, line in enumerate(lines):
            t0 = time.perf_counter_ns()
            proc.stdin.write(f"{line}\n> LATENCY {tp} 0 <\n")
            proc.stdin.flush()
            while True:
                out = proc.stdout.readline()
                if not out:
                    raise BrokenPipeError
                if out.startswith("> LATENCY "):
                    break
            lat_ns.append(time.perf_counter_ns() - t0)
            # > LATENCY tp ts ev tp cau sup ins ms <
            sup.append(int(out.split()[7]))
    except (BrokenPipeError, OSError):
        pass
    finally:
        timer.cancel()
        proc.kill()
    return {"formula": f.name, "timepoints": len(lines), "done": len(lat_ns),
            "timed_out": len(lat_ns) < len(lines), "wall_s": time.perf_counter() - started,
            "mean_us": sum(lat_ns) / len(lat_ns) / 1e3 if lat_ns else None,
            "max_us": max(lat_ns) / 1e3 if lat_ns else None, "sup": sup}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tools", default="enfflash,enfguard,dogwood")
    ap.add_argument("--policies", default=",".join(POLICIES))
    ap.add_argument("--timeout", type=float, default=600)
    args = ap.parse_args()
    tools = [t for t in args.tools.split(",") if t]
    for t in tools:
        if t not in EXE:
            raise SystemExit(f"unknown tool {t}")
    res = json.loads(OUT.read_text()) if OUT.exists() else {}
    # Runs are sequential: the timings must not compete for the CPU.
    for p in [p for p in args.policies.split(",") if p]:
        for tool in tools:
            r = run(tool, p, args.timeout)
            if r is None:
                res.setdefault(p, {}).pop(tool, None)
                print(f"{p:4} {tool:9} not expressible")
                continue
            res.setdefault(p, {})[tool] = r
            ref = res[p].get("enfflash")
            agree = ""
            if ref and tool != "enfflash":
                n = min(len(ref["sup"]), len(r["sup"]))
                bad = [i for i in range(n) if (ref["sup"][i] > 0) != (r["sup"][i] > 0)]
                r["disagree"] = bad
                agree = f"  disagree on {len(bad)} tps" if bad else "  same decisions"
            print(f"{p:4} {tool:9} {r['done']:5}/{r['timepoints']:<5} tps  "
                  f"mean {r['mean_us'] or 0:10.1f} us  max {r['max_us'] or 0:10.1f} us"
                  f"{'  TIMEOUT' if r['timed_out'] else ''}{agree}", flush=True)
            OUT.write_text(json.dumps(res))


if __name__ == "__main__":
    main()
