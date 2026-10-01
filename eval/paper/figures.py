#!/usr/bin/env python3
"""Figures for the paper's evaluation, one per table, drawn from the same
stored results as the tables.  The four panels are sized to share one page
(2 x 2, each 2.7 x 2.65 in, i.e. just under half the acmsmall text block).

Usage: figures.py {micro,app1,app2,app3} [-o OUT.pdf]

  micro  Table 1: EnfGuard suite; mean latency per formula and tool
  app1   Table 2: GDPRSocial; page latency = baseline + enforcement overhead
  app2   Table 3: EventManager; latency relative to EnfFlash vs. users, per view and tool
  app3   Table 4: LLM banking agent; latency per policy and tool, attacks prevented

Default output: $PAPER/figures/fig_<name>.pdf.
"""

import argparse
import glob
import json
import math
import os
import sys
from pathlib import Path

import matplotlib

matplotlib.use("pdf")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402
from matplotlib.patches import Patch  # noqa: E402

HOME = Path.home()
WHYENF = Path(os.environ.get("WHYENF", HOME / "Git/whyenf"))
PEL = Path(os.environ.get("PEL", HOME / "Git/proactive-enforcement-library"))
PAPER = Path(os.environ.get("PAPER", HOME / "Overleaf/Enfflash"))

SIZE = (2.7, 2.65)  # inches

# Palette (validated: categorical, light, white surface, all pairs).  Tools keep
# their color and marker in every panel; the monitor and the baseline are gray.
INK, INK2, MUTED, GRID, AXIS = "#0b0b0b", "#52514e", "#898781", "#e1e0d9", "#c3c2b7"
TOOL = {  # name: (label, color, marker)
    "enfflash": ("EnfFlash", "#2a78d6", "o"),
    "enfpoly":  ("Enfpoly",  "#4a3aa7", "s"),
    "enfguard": ("EnfGuard", "#eb6834", "^"),
    "dogwood":  ("Dogwood",  "#1baf7a", "D"),
    "cedar":    ("Cedar",    "#eda100", "v"),
    "monpoly":  ("Monpoly (monitor)", MUTED, "o"),
}

plt.rcParams.update({
    "font.family": "serif", "font.size": 7, "axes.titlesize": 7,
    "axes.labelsize": 7, "xtick.labelsize": 6.5, "ytick.labelsize": 6.5,
    "legend.fontsize": 6.5, "axes.edgecolor": AXIS, "axes.linewidth": 0.5,
    "xtick.color": INK2, "ytick.color": INK2, "axes.labelcolor": INK2,
    "text.color": INK, "xtick.major.width": 0.5, "ytick.major.width": 0.5,
    "xtick.minor.width": 0.3, "ytick.minor.width": 0.3,
    "xtick.major.size": 2, "ytick.major.size": 2, "xtick.minor.size": 1, "ytick.minor.size": 1,
    "pdf.fonttype": 42, "axes.spines.top": False, "axes.spines.right": False,
    "legend.frameon": False, "legend.handletextpad": 0.3, "legend.columnspacing": 0.8,
    "legend.borderaxespad": 0.2,
    # Text and math typeset by LaTeX in the paper's fonts (Type 1, as in acmart).
    "text.usetex": True,
    "text.latex.preamble": r"\usepackage[T1]{fontenc}\usepackage{libertine}\usepackage{xcolor}"
                           r"\usepackage[libertine]{newtxmath}",
})


def style(ax, grid_axis="y"):
    ax.grid(True, axis=grid_axis, which="major", color=GRID, linewidth=0.4)
    ax.set_axisbelow(True)


def log_ms_axis(ax, axis="y", label="latency (ms)"):
    """Log latency axis with ticks at powers of ten, labelled in ms/s."""
    def fmt(v, _):
        if v >= 1000:
            return f"{v / 1000:g} s"
        return f"{v:g}"
    getattr(ax, f"set_{axis}scale")("log")
    getattr(ax, f"{axis}axis").set_major_formatter(matplotlib.ticker.FuncFormatter(fmt))
    getattr(ax, f"{axis}axis").set_major_locator(matplotlib.ticker.LogLocator(base=10, numticks=12))
    getattr(ax, f"set_{axis}label")(label)


def tool_handle(tool, hollow=False, label=None):
    name, color, marker = TOOL[tool]
    return Line2D([], [], linestyle="none", marker=marker, markersize=3.6,
                  markerfacecolor="none" if (hollow or tool == "monpoly") else color,
                  markeredgecolor=color, markeredgewidth=0.7, label=label or name)


def scatter(ax, x, y, tool, hollow=False, size=11, z=3):
    _, color, marker = TOOL[tool]
    ax.scatter(x, y, s=size, marker=marker, zorder=z, linewidths=0.6,
               facecolors="none" if (hollow or tool == "monpoly") else color,
               edgecolors=color if (hollow or tool == "monpoly") else "white")


# ─── (a) Table 1: the EnfGuard suite ──────────────────────────────────────────

def fig_micro(out):
    sys.path.insert(0, str(WHYENF / "eval/enforcement"))
    os.chdir(WHYENF / "eval/enforcement")
    from all_tables import best_rows, DISPLAY_NAMES  # noqa: F401
    from suite import BENCHMARKS, ENFORCERS
    tools = ENFORCERS  # the monitor (Monpoly) solves a different problem: not shown
    fig, ax = plt.subplots(figsize=SIZE)
    x, groups, TO = 0, [], None
    points = {t: ([], []) for t in tools}
    timeouts = {t: [] for t in tools}
    for b in BENCHMARKS:
        rows = {t: best_rows(b, t) for t in tools}
        order = []
        for t in tools:
            if rows[t] is not None:
                order += [p for p in rows[t]["formula"].tolist() if p not in order]
        if not order:
            continue
        start = x
        for p in order:
            for t in tools:
                r = rows[t]
                m = r[r["formula"] == p] if r is not None else None
                if m is None or m.empty:
                    continue
                v = m.iloc[0]["avg_latency"]
                if v != v:  # NaN: ran, timed out
                    timeouts[t].append(x)
                else:
                    points[t][0].append(x)
                    points[t][1].append(v)
            x += 1
        groups.append((b, start, x - 1))
        x += 1.2  # gap between benchmarks
    ymin, ymax = 0.05, 300
    TO = ymax * 2.2
    for t in tools[::-1]:
        scatter(ax, points[t][0], points[t][1], t, size=16 if t == "enfflash" else 12,
                z=5 if t == "enfflash" else 3)
        # Timeouts on a band above the plot, one sub-row per tool.
        k = tools.index(t)
        scatter(ax, timeouts[t], [TO * (1.25 ** k)] * len(timeouts[t]), t, size=9, z=3)
    log_ms_axis(ax)
    ax.set_ylim(ymin, TO * 1.25 ** len(tools) * 1.1)
    ax.axhspan(TO / 1.25, TO * 1.25 ** len(tools) * 1.1, color="#f4f3ef", zorder=0, linewidth=0)
    ax.text(-1.0, TO * 1.25 ** 2, "t.o.", ha="right", va="center", color=INK2, fontsize=6.5)
    ax.set_yticks([t for t in ax.get_yticks() if ymin <= t <= ymax])
    ax.set_xlim(-1.5, x - 0.6)
    ax.set_xticks([])
    for b, s, e in groups:
        narrow = e - s < 3  # stagger the label of a narrow group below its neighbours
        ax.text((s + e) / 2, ymin / (1.35 if not narrow else 2.3), r"\textsc{%s}" % b,
                ha="center", va="top", color=INK2, fontsize=6.5)
        if s > 0:
            ax.axvline(s - 1.1, color=GRID, linewidth=0.4, zorder=0)
    style(ax)
    ax.set_title("(a) EnfGuard suite: mean latency per formula", loc="left", color=INK)
    handles = [tool_handle(t) for t in tools]
    ax.legend(handles=handles, loc="upper center", bbox_to_anchor=(0.44, -0.1), ncol=4,
              handlelength=1.0, columnspacing=0.6)
    fig.subplots_adjust(left=0.16, right=0.99, top=0.93, bottom=0.21)
    fig.savefig(out)


# ─── (b) Table 2: GDPRSocial ──────────────────────────────────────────────────

def fig_app1(out):
    suite = PEL / "miniTwitter_gdpr/benchmark/privacy_testsuite"
    sys.path.insert(0, str(suite))
    from make_table import ENTRYPOINTS, latest_run, load
    enf = load(latest_run(str(suite / "output"), "minitwit_gdpr"))
    base = load(latest_run(str(suite / "output"), "baseline"))
    ge = enf.groupby(["sc", "n"])["t_ms"].mean()
    gb = base.groupby(["sc", "n"])["t_ms"].mean()
    ns = sorted(enf["n"].unique().tolist())
    scs = [s for s in ENTRYPOINTS if s in set(enf["sc"])]
    fig, ax = plt.subplots(figsize=SIZE)
    w = 0.19
    for i, sc in enumerate(scs[::-1]):
        for j, n in enumerate(ns):
            y = i + (1.5 - j) * (w + 0.02)
            b = gb.get((sc, n), float("nan"))
            e = ge.get((sc, n), float("nan"))
            if e != e:
                continue
            b = b if b == b else 0.0
            ax.barh(y, b, height=w, color=AXIS, linewidth=0, zorder=2)
            ax.barh(y, max(e - b, 0), left=b, height=w, color=TOOL["enfflash"][1], linewidth=0,
                    zorder=2)
            ax.text(max(e, b) + 0.3, y, f"$10^{{{int(math.log10(n))}}}$", ha="left",
                    va="center", fontsize=5.5, color=INK2)
        label = ENTRYPOINTS[sc]
        ax.text(-0.6, i, label, ha="right", va="center", fontsize=6.5, color=INK)
    ax.set_yticks([])
    ax.set_ylim(-0.6, len(scs) - 0.4)
    ax.set_xlim(0, None)
    ax.set_xlabel("page latency (ms)")
    style(ax, "x")
    ax.spines["left"].set_visible(False)
    ax.set_title("(b) GDPRSocial: page latency", loc="left", color=INK)
    handles = [Patch(color=AXIS, label="non-enforced baseline"),
               Patch(color=TOOL["enfflash"][1], label="EnfFlash overhead")]
    ax.legend(handles=handles, loc="upper center", bbox_to_anchor=(0.36, -0.17), ncol=2,
              handlelength=0.9)
    ax.text(1.0, -0.25, "bars: $n$ posts", transform=ax.transAxes, ha="right", va="top",
            fontsize=6, color=INK2)
    fig.subplots_adjust(left=0.36, right=0.97, top=0.93, bottom=0.27)
    fig.savefig(out)


# ─── (c) Table 3: EventManager ────────────────────────────────────────────────

def fig_app2(out):
    suite = PEL / "event_platform/benchmark/privacy_testsuite"
    sys.path.insert(0, str(suite))
    from make_table import TOOLS, VIEWS, load_tool
    names = {"mfotl": "enfflash", "dogwood": "dogwood", "cedar": "cedar"}
    runs = {}
    for policy, _ in TOOLS:
        df = load_tool(str(suite / "output"), policy)
        if df is not None:
            runs[names[policy]] = df.groupby(["sc", "u"])["t_ms"].mean()
    scs = [s for s in VIEWS if any(s in set(r.index.get_level_values(0)) for r in runs.values())]
    # Latency relative to EnfFlash (1 = as fast as EnfFlash): on an absolute
    # log axis spanning ms to minutes, a 4x gap between two tools looks flat.
    # EnfFlash's own latency is printed along the bottom of each panel.  A tool
    # without a measurement at some n timed out (300 s per request, the
    # driver's REQ_TIMEOUT): marked x on the top edge.
    E = runs["enfflash"]
    TOP, BOTTOM, LABEL_Y = 16, 0.1, 0.14
    us = sorted({u for r in runs.values() for u in r.index.get_level_values(1)})
    blue = TOOL["enfflash"][1]

    def ms(v):
        return f"{v:.0f}" if v < 1000 else f"{v / 1000:.0f}\\,s"

    rows, cols = math.ceil(len(scs) / 2), 2
    fig, axes = plt.subplots(rows, cols, figsize=SIZE, sharex=True, sharey=True)
    axes = axes.flatten()
    for k, sc in enumerate(scs):
        ax = axes[k]
        e = E.loc[sc] if sc in E.index.get_level_values(0) else E.iloc[:0]
        ax.axhline(1, color=blue, linewidth=0.8, zorder=2)
        for u in us:
            txt = ms(e[u]) if u in e.index else "t.o."
            ax.text(u, LABEL_Y, txt, ha="center", va="center", fontsize=4.6, color=blue, zorder=5)
        for t in ["cedar", "dogwood"]:
            _, color, marker = TOOL[t]
            have = runs[t].loc[sc] if t in runs and sc in runs[t].index.get_level_values(0) else None
            done = set(have.index) if have is not None else set()
            for u in us:
                if u not in done:  # timed out
                    ax.plot([u], [TOP], marker="x", markersize=2.8, markeredgewidth=0.7,
                            color=color, zorder=4, clip_on=False)
            if have is None:
                continue
            r = (have / e).dropna()
            # Points above the axis (Cedar, up to 100x) sit on its top edge,
            # hollow and labelled with their value.
            ax.plot(r.index, r.clip(upper=TOP).values, color=color, linewidth=0.7, zorder=3, clip_on=False)
            for u, v in r.items():
                off = v > TOP
                ax.plot([u], [min(v, TOP)], marker=marker, markersize=2.6 if off else 2.4,
                        markerfacecolor="white" if off else color, markeredgecolor=color,
                        markeredgewidth=0.6 if off else 0, zorder=4, clip_on=False)
                if off:
                    ax.annotate(f"{v:.0f}$\\times$", (u, TOP), xytext=(0, -8), textcoords="offset points",
                                ha="center", fontsize=5, color=color)
            if t == "dogwood" and len(r):
                u, v = r.index[-1], r.values[-1]
                ax.annotate(f"{v:.1f}$\\times$", (u, v), xytext=(0, 3 if v >= 1 else -7),
                            textcoords="offset points", ha="center", fontsize=5.5, color=color)
        ax.set_title(VIEWS[sc], fontsize=6.5, color=INK, pad=1.5)
        style(ax)
        ax.set_xscale("log")
    for ax in axes[len(scs):]:
        ax.axis("off")
    axes[0].set_yscale("log")
    axes[0].set_ylim(BOTTOM, TOP)
    axes[0].yaxis.set_major_locator(matplotlib.ticker.FixedLocator([0.25, 1, 4, 16]))
    axes[0].yaxis.set_major_formatter(matplotlib.ticker.FuncFormatter(lambda v, _: f"{v:g}$\\times$"))
    axes[0].yaxis.set_minor_locator(matplotlib.ticker.NullLocator())
    for ax in axes:
        ax.set_xticks(us)
        ax.set_xlim(us[0] / 2.2, us[-1] * 2.2)
        ax.xaxis.set_major_formatter(matplotlib.ticker.FuncFormatter(lambda v, _: f"{v:g}"))
        ax.xaxis.set_minor_locator(matplotlib.ticker.NullLocator())
    fig.supylabel("latency / EnfFlash latency", fontsize=7, color=INK2, x=0.02)
    fig.supxlabel("users $n$ \\quad {\\color[HTML]{%s}(numbers: EnfFlash latency in ms)}" % blue[1:],
                  fontsize=7, color=INK2, y=0.07)
    fig.suptitle("(c) EventManager: latency relative to EnfFlash", x=0.02, ha="left", fontsize=7, y=0.985)
    enf = Line2D([], [], color=blue, linewidth=0.8, label="EnfFlash")
    to = Line2D([], [], linestyle="none", marker="x", markersize=3, markeredgewidth=0.7, color=MUTED,
                label="t.o. (300\\,s)")
    fig.legend(handles=[enf, tool_handle("dogwood"), tool_handle("cedar"), to],
               loc="lower center", bbox_to_anchor=(0.55, -0.01), ncol=4, handlelength=1.0)
    fig.subplots_adjust(left=0.17, right=0.98, top=0.9, bottom=0.19, hspace=0.62, wspace=0.12)
    fig.savefig(out)


# ─── (d) Table 4: LLM banking agent ───────────────────────────────────────────

def fig_app3(out):
    bank = WHYENF / "eval/agent_banking"
    sys.path.insert(0, str(bank))
    from report import NAMES, ORDER, DOGWOOD_PARTIAL
    res = bank / "results"
    cmp = json.loads((res / "compare.json").read_text()) if (res / "compare.json").exists() else {}
    base = {r["run"]: r for r in json.loads((res / "none.json").read_text())["runs"]}
    succ0 = {k for k, r in base.items() if r["injection_task"] and r["attack_success"]}
    prevented = {}
    for p in ORDER:
        f = res / f"{p}.json"
        if f.exists():
            runs = {r["run"]: r for r in json.loads(f.read_text())["runs"]}
            prevented[p] = sum(1 for k in succ0 if not runs[k]["attack_success"])
    policies = [p for p in ORDER if p in prevented]
    fig, ax = plt.subplots(figsize=SIZE)
    TO = 2e4
    for i, p in enumerate(policies):
        y = len(policies) - 1 - i + (0 if p != "all" else -0.35)
        for k, t in enumerate(["enfguard", "dogwood", "enfflash"]):
            r = cmp.get(p, {}).get(t)
            if r is None:
                continue
            v = TO * 1.35 ** k if r["timed_out"] else r["mean_us"] / 1000
            scatter(ax, [v], [y], t, hollow=(t == "dogwood" and p in DOGWOOD_PARTIAL),
                    size=14 if t == "enfflash" else 11, z=5 if t == "enfflash" else 3)
        ax.text(-0.01, y, p.upper() if p != "all" else "All", transform=ax.get_yaxis_transform(),
                ha="right", va="center", fontsize=6.5, color=INK)
        ax.text(1.1, y, f"{prevented[p]}", transform=ax.get_yaxis_transform(),
                ha="right", va="center", fontsize=6.5, color=INK2)
    ax.text(1.1, len(policies) - 0.35, "prev.", transform=ax.get_yaxis_transform(),
            ha="right", va="bottom", fontsize=6.5, color=INK2)
    log_ms_axis(ax, "x")
    ax.set_xlim(0.03, TO * 1.35 ** 3)
    ax.axvspan(TO / 1.3, TO * 1.35 ** 3, color="#f4f3ef", zorder=0, linewidth=0)
    ax.text(TO * 1.35, -1.1, "t.o.", ha="center", va="top", color=INK2, fontsize=6.5)
    ax.set_xticks([t for t in [0.1, 1, 10, 100, 1000, 10000]])
    ax.set_yticks([])
    ax.set_ylim(-1.0, len(policies) - 0.3)
    ax.spines["left"].set_visible(False)
    style(ax, "x")
    ax.axhline(0.3, color=GRID, linewidth=0.4)
    ax.set_title("(d) LLM banking agent: mean latency per policy", loc="left", color=INK)
    handles = [tool_handle("enfflash"), tool_handle("enfguard"), tool_handle("dogwood"),
               tool_handle("dogwood", hollow=True, label="Dogwood, suppression only")]
    ax.legend(handles=handles, loc="upper center", bbox_to_anchor=(0.45, -0.17), ncol=2,
              handlelength=1.0)
    fig.subplots_adjust(left=0.1, right=0.87, top=0.93, bottom=0.28)
    fig.savefig(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("figure", choices=["micro", "app1", "app2", "app3"])
    ap.add_argument("-o", "--output")
    args = ap.parse_args()
    out = Path(args.output) if args.output else PAPER / "figures" / f"fig_{args.figure}.pdf"
    out.parent.mkdir(parents=True, exist_ok=True)
    {"micro": fig_micro, "app1": fig_app1, "app2": fig_app2, "app3": fig_app3}[args.figure](str(out))
    print(f"[figures] wrote {out}")


if __name__ == "__main__":
    main()
