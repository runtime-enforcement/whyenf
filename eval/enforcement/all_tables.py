#!/usr/bin/env python3
"""Build the per-policy LaTeX comparison table for `tab:micro` from the CSVs in
`outputs/<benchmark>/<tool>/summary.csv`.

Run from `eval/enforcement/`:

    python3 all_tables.py            # print LaTeX to stdout
    python3 all_tables.py -o tab_micro.tex

Each summary.csv holds, for one (tool, benchmark), the per-(policy, log,
acceleration) latency stats produced by `evaluation.run_experiments`.  We reuse
`evaluation.table` to pick, for every policy, the row at the *maximal real-time
acceleration* (the largest acceleration whose max latency still meets the
real-time bound), then emit one LaTeX line per policy with `mean (max)` latency
in milliseconds for every tool.

Cell legend:
  * ``mean (max)`` — latency in ms at the policy's maximal real-time acceleration
  * ``t.o.``       — the tool ran the policy but never met the real-time bound
  * ``--``         — the tool was not evaluated on this policy
"""

import argparse
import math
import os
from typing import Dict, List, Optional

import pandas as pd

from evaluation import table

# Benchmarks (in order) and the tools (column order) shown in tab:micro.
BENCHMARKS: List[str] = ["gdpr", "fun", "cluster", "agg", "nokia", "ic"]
TOOLS: List[str] = ["enfflash", "monpoly", "enfpoly", "enfguard"]
TOOL_HEADERS: Dict[str, str] = {
    "enfflash": "Enfflash",
    "monpoly":  "Monpoly",
    "enfpoly":  "Enfpoly",
    "enfguard": "EnfGuard",
}

OUTPUTS = "outputs"


def best_rows(benchmark: str, tool: str) -> Optional[pd.DataFrame]:
    """Per-policy best real-time row for one (benchmark, tool), or None."""
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
    """Format one tool's cell for a policy (bold = fastest tool on this row)."""
    if row is None:                       # tool did not run this policy
        return "-- & "
    if pd.isna(row["avg_latency"]):       # ran, but never real-time
        return "t.o. & "
    cell1 = f"{row['avg_latency']:.2f}"
    cell2 = f"({row['max_latency']:.0f})"
    return (r"\textbf{%s} & %s"  if bold else r"%s & %s") % (cell1, cell2)


def policy_name(p: str) -> str:
    return p.replace("_", r"\_")


def build() -> str:
    # Gather best-row tables: results[benchmark][tool] -> DataFrame (or None).
    results: Dict[str, Dict[str, Optional[pd.DataFrame]]] = {}
    for b in BENCHMARKS:
        results[b] = {tool: best_rows(b, tool) for tool in TOOLS}

    lines: List[str] = []
    lines.append(r"\begin{tabular}{l" + "r" * (2 * len(TOOLS)) + "}")
    lines.append(r"\toprule")
    header = "Policy & " + " & ".join(r"\multicolumn{2}{c}{%s}" % TOOL_HEADERS[t] for t in TOOLS) + r" \\"
    lines.append(header)

    for b in BENCHMARKS:
        per_tool = results[b]
        # Union of policies seen for this benchmark, in enfflash's order if present.
        ordered: List[str] = []
        seen = set()
        for tool in TOOLS:
            t = per_tool[tool]
            if t is None:
                continue
            for p in t["formula"].tolist():
                if p not in seen:
                    seen.add(p)
                    ordered.append(p)
        if not ordered:
            continue  # benchmark not run yet — skip silently

        lines.append(r"\midrule")
        lines.append(r"\multicolumn{%d}{l}{\emph{\textsc{%s}}} \\" % (2 * len(TOOLS) + 1, b))

        for p in ordered:
            # Resolve each tool's row for this policy, then bold the fastest
            # (lowest mean latency) among the tools with a real-time number.
            rows: Dict[str, Optional[pd.Series]] = {}
            for tool in TOOLS:
                t = per_tool[tool]
                row = None
                if t is not None:
                    match = t[t["formula"] == p]
                    if not match.empty:
                        row = match.iloc[0]
                rows[tool] = row

            best_tool = None
            best_lat = math.inf
            for tool in TOOLS:
                row = rows[tool]
                if row is not None and not pd.isna(row["avg_latency"]):
                    if row["avg_latency"] < best_lat:
                        best_lat = row["avg_latency"]
                        best_tool = tool

            cells = [fmt_cell(rows[tool], bold=(tool == best_tool)) for tool in TOOLS]
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
