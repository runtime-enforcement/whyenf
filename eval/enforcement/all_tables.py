#!/usr/bin/env python3
"""Build the per-policy LaTeX comparison table `tab:micro` (Table 1) from the
CSVs in `outputs/<benchmark>/<tool>/summary.csv`.

Run from `eval/enforcement/`:

    python3 all_tables.py            # print LaTeX to stdout
    python3 all_tables.py -o tab_micro.tex

Each summary.csv holds, for one (tool, benchmark), the per-(policy, log)
latency stats produced by `evaluation.run_experiments`.  For every policy we
emit `mean (max)` latency in milliseconds for every tool: first the enforcers
(`suite.ENFORCERS`), then, separated by a double vertical line, the monitors
(`suite.MONITORS`).  The fastest enforcer of each row is in bold.

Cell legend:
  * ``mean (max)`` — latency in ms
  * ``t.o.``       — the tool ran the policy but timed out
  * ``--``         — the tool does not support the policy (or was not run)
"""

import argparse
import math
import os
from typing import Dict, List, Optional

import pandas as pd

from evaluation import table
from suite import BENCHMARKS, ENFORCERS, MONITORS, HEADERS

OUTPUTS = "outputs"


def best_rows(benchmark: str, tool: str) -> Optional[pd.DataFrame]:
    """Per-policy rows for one (benchmark, tool), or None."""
    fn = os.path.join(OUTPUTS, benchmark, tool, "summary.csv")
    if not os.path.exists(fn):
        return None
    try:
        df = pd.read_csv(fn)
    except (pd.errors.EmptyDataError, OSError):
        return None
    if df.empty:
        return None
    t = table(df).copy()
    for col in ("avg_latency", "max_latency"):
        t[col] = pd.to_numeric(t[col], errors="coerce")
    return t


def fmt_cell(row: Optional[pd.Series], bold: bool = False) -> str:
    """Format one tool's two cells for a policy."""
    if row is None:                       # tool did not run this policy
        return "-- & "
    if pd.isna(row["avg_latency"]):       # ran, but timed out
        return "t.o. & "
    cell1 = f"{row['avg_latency']:.2f}"
    cell2 = f"({row['max_latency']:.0f})"
    return (r"\textbf{%s} & %s" if bold else r"%s & %s") % (cell1, cell2)


# Row labels that differ from the formula file name.
DISPLAY_NAMES: Dict[str, str] = {"logging_behavior__exe": "logging_behavior"}


def policy_name(p: str) -> str:
    return DISPLAY_NAMES.get(p, p).replace("_", r"\_")


def build() -> str:
    tools = ENFORCERS + MONITORS
    results: Dict[str, Dict[str, Optional[pd.DataFrame]]] = {
        b: {tool: best_rows(b, tool) for tool in tools} for b in BENCHMARKS}

    spec = "l" + "r" * (2 * len(ENFORCERS)) + "||" + "r" * (2 * len(MONITORS))
    lines: List[str] = []
    lines.append(r"\begin{tabular}{%s}" % spec)
    lines.append(r"\toprule")
    lines.append(r" & \multicolumn{%d}{c||}{Enforcement} & \multicolumn{%d}{c}{Monitoring} \\"
                 % (2 * len(ENFORCERS), 2 * len(MONITORS)))
    heads = []
    for i, t in enumerate(tools):
        bar = "||" if i == len(ENFORCERS) - 1 else ""
        heads.append(r"\multicolumn{2}{c%s}{%s}" % (bar, HEADERS[t]))
    lines.append("Policy & " + " & ".join(heads) + r" \\")

    for b, params in BENCHMARKS.items():
        per_tool = results[b]
        # Union of the policies seen for this benchmark, in tool order.
        ordered: List[str] = []
        for tool in tools:
            t = per_tool[tool]
            if t is not None:
                ordered += [p for p in t["formula"].tolist() if p not in ordered]
        if not ordered:
            continue  # benchmark not run yet

        lines.append(r"\midrule")
        # Keep the || between enforcers and monitors on the benchmark's row.
        lines.append(r"\multicolumn{%d}{l||}{\emph{\textsc{%s} (timeout = %d s)}} & \multicolumn{%d}{l}{} \\"
                     % (1 + 2 * len(ENFORCERS), b, params["to"], 2 * len(MONITORS)))
        for p in ordered:
            rows: Dict[str, Optional[pd.Series]] = {}
            for tool in tools:
                t = per_tool[tool]
                match = t[t["formula"] == p] if t is not None else None
                rows[tool] = match.iloc[0] if match is not None and not match.empty else None
            best_tool, best_lat = None, math.inf
            for tool in ENFORCERS:
                row = rows[tool]
                if row is not None and not pd.isna(row["avg_latency"]) and row["avg_latency"] < best_lat:
                    best_tool, best_lat = tool, row["avg_latency"]
            cells = [fmt_cell(rows[tool], bold=(tool == best_tool)) for tool in tools]
            lines.append(policy_name(p) + " & " + " & ".join(cells) + r" \\")

    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    return "\n".join(lines)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("-o", "--output", help="write LaTeX here instead of stdout")
    args = ap.parse_args()
    latex = build()
    if args.output:
        with open(args.output, "w") as f:
            f.write(latex + "\n")
        print(f"[all_tables] wrote {args.output}")
    else:
        print(latex)


if __name__ == "__main__":
    main()
