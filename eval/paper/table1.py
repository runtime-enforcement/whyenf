#!/usr/bin/env python3
"""Table 1 (tab:micro): the EnfGuard benchmark suite.

Reruns the measurements of the selected tools on the selected benchmarks
(eval/enforcement/outputs/<benchmark>/<tool>/summary.csv is overwritten), then
regenerates the full LaTeX table from all stored results.  Use table1.sh, which
also pins the CPU governor.

    table1.py --tools enfflash,dogwood            # rerun two tools, all benchmarks
    table1.py --tools dogwood --benchmarks ic     # rerun one tool on one benchmark
    table1.py                                     # only regenerate the table
"""
import argparse
import os
import sys
from pathlib import Path

ENF = Path(__file__).resolve().parent.parent / "enforcement"
os.chdir(ENF)
sys.path.insert(0, str(ENF))

from suite import BENCHMARKS, ENFORCERS, MONITORS, EXES, N  # noqa: E402

TOOLS = ENFORCERS + MONITORS


def parse_list(arg: str, all_values: list, what: str) -> list:
    if arg == "all":
        return list(all_values)
    values = [v for v in arg.split(",") if v]
    unknown = [v for v in values if v not in all_values]
    if unknown:
        sys.exit(f"unknown {what}: {', '.join(unknown)} (choose from {', '.join(all_values)})")
    return values


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tools", default="",
                    help=f"tools to rerun, comma-separated, or 'all' ({','.join(TOOLS)}); default: none")
    ap.add_argument("--benchmarks", default="all",
                    help=f"benchmarks to rerun ({','.join(BENCHMARKS)}); default: all")
    ap.add_argument("-n", type=int, default=N, help=f"repetitions per (formula, log); default {N}")
    tables = os.environ.get("TABLES", os.path.expanduser("~/Overleaf/Enfflash/tables"))
    ap.add_argument("-o", "--output", default=os.path.join(tables, "tab_micro.tex"),
                    help="LaTeX output (default: $TABLES/tab_micro.tex, i.e. the paper's tables/)")
    args = ap.parse_args()

    tools = parse_list(args.tools, TOOLS, "tools") if args.tools else []
    benchmarks = parse_list(args.benchmarks, list(BENCHMARKS), "benchmarks")

    if tools:
        from evaluation import run_experiments  # refuses to run unless the governor is `performance`
        for b in benchmarks:
            for tool in tools:
                if not (Path("benchmarks") / b / tool / "formulae").is_dir():
                    print(f"[table1] {tool} has no formulae for {b}: skipped")
                    continue
                exe = EXES[tool]
                if not os.path.exists(exe):
                    sys.exit(f"[table1] executable {exe} for {tool} not found")
                params = BENCHMARKS[b]
                print(f"[table1] running {tool} on {b} (n = {args.n})")
                run_experiments(option=tool, benchmark=b, exe=exe, n=args.n,
                                time_unit=params["time_unit"], to=params["to"], func=params["func"])

    import all_tables
    latex = all_tables.build()
    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(latex + "\n")
    print(f"[table1] wrote {out}")


if __name__ == "__main__":
    main()
