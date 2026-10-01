"""Summarize results/*.json (from replay.py) into a table.

For each policy: attacks prevented (among those that succeed without
enforcement), benign runs that lost utility or had a call blocked, utility
under attack, caused events by kind, and the per-time-point latency of the
enforcer (mean and max, in microseconds).

Usage: report.py [results/] [--latex [-o OUT.tex]]
"""

import json
import sys
from collections import Counter
from pathlib import Path

ORDER = ["b1", "b2", "b3", "b4", "b5", "b6", "b7", "b8", "b9", "b10", "all"]
NAMES = {
    "b1": "Payee provenance", "b2": "No leak in subject", "b3": "Daily cap per payee",
    "b4": "Velocity", "b5": "Standing-order redirect", "b6": "Password change",
    "b7": "Cool-down after credential change", "b8": "Quarantine", "b9": "Audit",
    "b10": "Invoice consistency", "all": "All (B1-B10)",
}


def load(d: Path, name: str) -> dict:
    return json.loads((d / f"{name}.json").read_text())


def main() -> None:
    argv = sys.argv[1:]
    out_file = None
    if "-o" in argv:
        i = argv.index("-o")
        out_file = argv[i + 1]
        del argv[i:i + 2]
    args = [a for a in argv if not a.startswith("--")]
    latex = "--latex" in argv
    d = Path(args[0]) if args else Path(__file__).parent / "results"
    base = {r["run"]: r for r in load(d, "none")["runs"]}
    cmp_file = d / "compare.json"
    cmp = json.loads(cmp_file.read_text()) if cmp_file.exists() else {}

    def offline(p: str, tool: str) -> str:
        """Replay of the recorded log: mean latency per time-point (us)."""
        r = cmp.get(p, {}).get(tool)
        if r is None:
            return "--"
        if r["timed_out"]:
            return f"t.o.({r['done']}/{r['timepoints']})"
        return f"{r['mean_us']:.0f}"
    succ0 = {k for k, r in base.items() if r["injection_task"] and r["attack_success"]}
    rows = []
    for p in ORDER:
        f = d / f"{p}.json"
        if not f.exists():
            continue
        data = load(d, p)
        runs = {r["run"]: r for r in data["runs"]}
        prevented = sum(1 for k in succ0 if not runs[k]["attack_success"])
        benign = [r for r in runs.values() if not r["injection_task"]]
        fp = sum(1 for r in benign if r["blocked"] or not r["utility"])
        attacked = [r for r in runs.values() if r["injection_task"]]
        util_att = sum(r["utility"] for r in attacked)
        caused = Counter(c[0] for r in runs.values() for c in r["caused"])
        lat = data["latencies_ns"]
        mean = sum(lat) / len(lat) / 1000 if lat else 0.0
        mx = max(lat) / 1000 if lat else 0.0
        rows.append((p, prevented, len(succ0), fp, len(benign), util_att, len(attacked),
                     dict(caused), mean, mx, len(lat),
                     " / ".join(offline(p, t) for t in ("enfflash", "enfguard", "dogwood"))))

    base_util = sum(r["utility"] for r in base.values() if r["injection_task"])
    if latex:
        tex = latex_table(rows, cmp, d, len(succ0), base_util)
        if out_file:
            Path(out_file).write_text(tex)
            print(f"wrote {out_file}")
        else:
            print(tex, end="")
        return
    print(f"baseline (no enforcement): {len(succ0)} successful attacks, "
          f"utility under attack {base_util}/{len(base) - 16}")
    print(f"{'policy':<36} {'prevented':>9} {'benign FP':>9} {'util@att':>9}  "
          f"{'latency us mean (max)':>22} {'replay us E / G / D':>26}  caused")
    for p, prev, tot, fp, nb, ua, na, caused, mean, mx, n, eg in rows:
        c = ", ".join(f"{v} {k}" for k, v in sorted(caused.items()))
        print(f"{p.upper() + ' ' + NAMES[p]:<36} {prev:>4}/{tot:<4} {fp:>4}/{nb:<4} {ua:>4}/{na:<4} "
              f"{mean:>12.1f} ({mx:>6.0f}) {eg:>26}  {c}")


# Dogwood cannot cause events: only the suppression part of these is translated.
DOGWOOD_PARTIAL = {"b5", "b6", "b8", "all"}
TOOLS = ["enfflash", "enfguard", "dogwood"]


def latex_table(rows, cmp, d: Path, n_attacks: int, base_util: int) -> str:
    """The LaTeX tabular: one row per policy and one for their conjunction,
    with the attack outcomes of the runs (Enfflash) and the latency, in ms,
    of Enfflash, EnfGuard and Dogwood on the recorded logs, `mean (max)`, in
    the format of Table 1 (fastest enforcer in bold)."""
    def cells(p, tool, bold):
        r = cmp.get(p, {}).get(tool)
        if r is None:
            return "-- & "
        if r["timed_out"] or r["mean_us"] is None:
            return "t.o. & "
        mean = f"{r['mean_us'] / 1000:.2f}"
        if bold:
            mean = f"\\textbf{{{mean}}}"
        if tool == "dogwood" and p in DOGWOOD_PARTIAL:
            mean += "$^\\dagger$"
        mx = r["max_us"] / 1000
        return f"{mean} & ({mx:.0f})" if mx >= 1 else f"{mean} & ({mx:.1f})"

    lines = [
        "\\begin{tabular}{ll|rrr|rrrrrr}",
        "\\toprule",
        "& Policy & \\multicolumn{1}{c}{Prev.} & \\multicolumn{1}{c}{FP} & "
        "\\multicolumn{1}{c|}{Util.} & \\multicolumn{2}{c}{Enfflash} & "
        "\\multicolumn{2}{c}{EnfGuard} & \\multicolumn{2}{c}{Dogwood} \\\\",
        "\\midrule",
        f"-- & No enforcement & 0/{n_attacks} & 0/16 & {base_util}/144 & & & & & & \\\\",
    ]
    for p, prev, tot, fp, nb, ua, na, *_ in rows:
        if p == "all":
            lines.append("\\midrule")
        done = {t: cmp.get(p, {}).get(t) for t in TOOLS}
        means = {t: r["mean_us"] for t, r in done.items()
                 if r and not r["timed_out"] and r["mean_us"] is not None}
        best = min(means, key=means.get) if means else None
        name = NAMES[p].replace("B1-B10", "B1--B10")
        lat = " & ".join(cells(p, t, t == best) for t in TOOLS)
        lines.append(f"{'--' if p == 'all' else p.upper()} & {name} & {prev}/{tot} & {fp}/{nb} & "
                     f"{ua}/{na} & {lat} \\\\")
    lines += ["\\bottomrule", "\\end{tabular}", ""]
    return "\n".join(lines)


if __name__ == "__main__":
    main()
