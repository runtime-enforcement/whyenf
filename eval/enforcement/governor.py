"""Refuse to run measurements unless every CPU uses the `performance` governor.

Under `powersave` the clock idles at a fraction of its maximum and ramps up
unpredictably, which distorts latency measurements.  `require_performance()`
checks every CPU; if one is not on `performance`, it tries to switch them with
`sudo -n cpupower frequency-set -g performance` (no password prompt) and aborts
if that does not work.
"""
import glob
import subprocess
import sys


def governors():
    """The scaling governor of each CPU (empty if cpufreq is unavailable)."""
    out = {}
    for path in sorted(glob.glob("/sys/devices/system/cpu/cpu[0-9]*/cpufreq/scaling_governor")):
        with open(path) as f:
            out[path.split("/")[5]] = f.read().strip()
    return out


def require_performance():
    govs = governors()
    if not govs:
        sys.exit("ERROR: cannot read the CPU scaling governor (no cpufreq in /sys); refusing to run.")
    if all(g == "performance" for g in govs.values()):
        return
    subprocess.run(["sudo", "-n", "cpupower", "frequency-set", "-g", "performance"],
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    govs = governors()
    bad = sorted({g for g in govs.values() if g != "performance"})
    if bad:
        sys.exit(f"ERROR: CPU governor is {', '.join(bad)}, not performance; refusing to run.\n"
                 "Run `sudo cpupower frequency-set -g performance` first.")


if __name__ == "__main__":
    require_performance()
    print("CPU governor: performance")
