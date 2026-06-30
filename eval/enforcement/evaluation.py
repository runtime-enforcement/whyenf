import os.path
from pathlib import Path
from tqdm import tqdm
import gc

from typing import Any, Dict, List, Optional

import pandas as pd
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from replayer import replay

plt.rcParams["font.family"] = "serif"
plt.rcParams["font.serif"] = "Times New Roman"
plt.rcParams["text.usetex"] = True


def summary(df: pd.DataFrame, time_unit: float) -> Dict[str, Any]:
    d1 = time_unit * 1000
    duration = df["time"].max() - df["time"].min()

    return {
        "d1": d1,
        "n_ev": df["n_ev"].sum(),
        "n_tp": df["n_tp"].sum(),
        "cau": df["cau"].sum(),
        "sup": df["sup"].sum(),
        "ins": df["ins"].sum(),
        "avg_ev": 0 if duration == 0 else df["n_ev"].sum() / duration * 1000,
        "avg_latency": df["latency"].mean(),
        "avg_time": df["out_time"].diff().mean(),
        "max_time": df["out_time"].diff().max(),
        "max_latency": df["latency"].max(),
        "real_time": df["latency"].max() <= d1,
    }


def summary_to(formula_desc: str, log_desc: str, time_unit: float) -> Dict[str, Any]:
    return {
        "d1": time_unit * 1000,
        "n_ev": 0,
        "n_tp": 0,
        "cau": 0,
        "sup": 0,
        "ins": 0,
        "avg_ev": 0,
        "avg_latency": "t.o.",
        "avg_time": "t.o.",
        "max_time": "t.o.",
        "max_latency": "t.o.",
        "real_time": False,
        "formula": formula_desc,
        "log": log_desc,
    }


def table(df: pd.DataFrame) -> pd.DataFrame:
    df = df.copy()

    metric_cols = ["avg_latency", "max_latency", "avg_time", "max_time", "avg_ev", "d1"]
    for col in metric_cols:
        df[col] = pd.to_numeric(df[col], errors="coerce")

    series = []

    for (formula, log), formula_log_df in df.groupby(["formula", "log"]):
        numeric_df = formula_log_df.dropna(subset=["max_latency"])

        if numeric_df.empty:
            series.append(pd.Series({
                "formula": formula,
                "log": log,
                "a": "t.o.",
                "real_time": False,
                "avg_latency": "t.o.",
                "max_latency": "t.o.",
                "avg_time": "t.o.",
                "max_time": "t.o.",
                "avg_ev": "t.o.",
            }))
            continue

        avg_s = numeric_df.mean(numeric_only=True)

        series.append(pd.Series({
            "formula": formula,
            "log": log,
            "avg_latency": avg_s["avg_latency"],
            "max_latency": avg_s["max_latency"],
            "avg_time": avg_s["avg_time"],
            "max_time": avg_s["max_time"],
            "avg_ev": avg_s["avg_ev"],
        }))

    return pd.DataFrame(series)


def run_tool(
    command: str,
    log: Path,
    desc: str,
    to: int,
    verbose: bool,
) -> Optional[pd.DataFrame]:
    print(command)

    max_tp = len(open(log, "r").readlines()) - 1
    df = replay(log, max_tp, command, desc=desc, to=to, verbose=verbose)

    if df is None:
        return None

    df_f = df[df["type"] == "f"]
    df_r = df[df["type"] == "r"]

    merged_df = df_f.merge(df_r, on="tp", suffixes=("_f", "_r"))

    result_df = pd.DataFrame({
        "tp": merged_df["tp"],
        "n_ev": merged_df["n_ev_r"],
        "n_tp": merged_df["n_tp_r"],
        "cau": merged_df["cau_r"],
        "sup": merged_df["sup_r"],
        "ins": merged_df["ins_r"],
        "time": merged_df["ts_f"],
        "latency": merged_df["computer_time_r"] - merged_df["computer_time_f"],
        "out_time": merged_df["computer_time_r"],
    })

    return result_df.sort_values(by="tp")


def name_of_time_unit(time_unit: int) -> str:
    if time_unit == 1:
        return "seconds"
    elif time_unit == 60:
        return "minutes"
    elif time_unit == 60 * 60:
        return "hours"
    elif time_unit == 60 * 60 * 24:
        return "days"
    elif time_unit == 60 * 60 * 24 * 365:
        return "years"
    else:
        return ""


def plot(formula: str, log: str, df: pd.DataFrame, fn: Path, time_unit: int) -> None:
    df = df.copy()

    fig, ax = plt.subplots(1, 1, figsize=(7.5, 2.5))

    real_time = 1000 * time_unit
    df["time"] /= 1000

    ax.plot(df["time"], df["latency"], "k-", label="latency (ms)", linewidth=0.5)
    ax.plot(
        [min(df["time"]), max(df["time"])],
        [real_time, real_time],
        "k:",
        label="real-time latency $1/a$ (ms)",
        linewidth=0.5,
    )
    ax.plot(
        [min(df["time"]), max(df["time"])],
        [max(df["latency"]), max(df["latency"])],
        "k--",
        label=r"max latency $\mathsf{max}_{\ell}(a)$ (ms)",
        linewidth=0.5,
    )

    df_ev = df[df["n_ev"] > 0]
    ax.plot(df_ev["time"], df_ev["n_ev"], "b|", label="trace events", markersize=2)

    df_cau = df[df["cau"] > 0]
    ax.plot(df_cau["time"], df_cau["cau"], "go", label="caused events", markersize=2)

    df_sup = df[df["sup"] > 0]
    ax.plot(df_sup["time"], df_sup["sup"], "r^", label="suppressed events", markersize=2)

    ax.set_xlabel("time elapsed (s)")
    ax.set_title(
        f"Formula = {formula}, log = {log}"
        f"(1 second = {1 / time_unit:.0f} {name_of_time_unit(time_unit)})"
    )
    ax.legend(loc="upper left")

    fig.tight_layout()
    fig.savefig(str(fn), dpi=1000)
    plt.close()


def run_experiments(
    option: str,
    benchmark: str,
    exe: str,
    only_graph: bool = False,
    n: int = 10,
    time_unit: int = 1,
    to: int = 900,
    func: bool = False,
    verbose: bool = False,
    smoke_test: bool = False,
) -> Optional[pd.DataFrame]:

    benchmark_path = Path("benchmarks") / benchmark / option
    formulae_path = benchmark_path / "formulae"
    logs_path = benchmark_path / "logs"
    out_path = Path("outputs") / benchmark / option

    if not os.path.exists(out_path):
        os.makedirs(out_path)

    summary_csv_fn = out_path / "summary.csv"

    command: str = ""

    if option == "enfpoly":
        command = exe + " -enforce -sig {} -formula " + str(formulae_path) + "/{} -ignore_parse_errors"
    elif option == "monpoly":
        command = exe + " -sig {} -formula " + str(formulae_path) + "/{} -ignore_parse_errors"
    elif option == "whyenf":
        command = exe + " -sig {} -formula " + str(formulae_path) + "/{}"
    elif option == "enfguard":
        command = exe + " -sig {} -formula " + str(formulae_path) + "/{}"
    elif option == "enfflash":
        command = exe + " -sig {} -formula " + str(formulae_path) + "/{}"
    else:
        raise ValueError("Invalid option " + option)

    if func:
        command += " -func " + str(benchmark_path / "functions.py")

    formulae: Dict[str, str] = {fn.split(".")[0]: fn for fn in os.listdir(formulae_path)}
    logs: Dict[str, str] = {fn.split(".")[0]: fn for fn in os.listdir(logs_path)}
    sig_fn: Path = benchmark_path / "signature.sig"

    if smoke_test:
        first_log_key, first_log = list(logs.items())[0]
        logs = {first_log_key: first_log}

        first_formula_key, first_formula = list(formulae.items())[0]
        formulae = {first_formula_key: first_formula}

    series: List[Dict[str, Any]] = []

    total_steps = len(formulae) * len(logs) * n
    desc = (
        f"option = {option}, benchmark = {benchmark}, n = {n}"
    )
    t: tqdm = tqdm(total=total_steps, desc=desc)

    if not only_graph:
        for formula_desc, formula_fn in formulae.items():
            for log_desc, log_fn in logs.items():
                ran_any = False

                for i in range(n):
                    run_desc = (
                        f"formula = {formula_desc}, log = {log_desc}, it = {i + 1}"
                    )

                    df = run_tool(
                        command.format(sig_fn, formula_fn),
                        logs_path / log_fn,
                        run_desc,
                        to=to,
                        verbose=verbose,
                    )

                    if df is not None:
                        csv_fn = f"{formula_desc}_{log_desc}_it{i + 1}.csv"
                        png_fn = f"{formula_desc}_{log_desc}_it{i + 1}.png"

                        df.to_csv(out_path / csv_fn, index=False)

                        summ = summary(df, time_unit)
                        summ["formula"] = formula_desc
                        summ["log"] = log_desc
                        summ["it"] = i + 1

                        plot(formula_desc, log_desc, df, out_path / png_fn, time_unit)

                        series.append(summ)
                        ran_any = True

                        print(summ)

                    t.update()
                    gc.collect()

                if not ran_any:
                    series.append(summary_to(formula_desc, log_desc, time_unit))

        summary_df = pd.DataFrame(series)
        summary_df.to_csv(summary_csv_fn, index=False)

    t.close()

    if not os.path.exists(summary_csv_fn):
        print(
            f"[skip] no results to summarize for option = {option}, "
            f"benchmark = {benchmark} (expected {summary_csv_fn})."
        )
        return None

    try:
        summary_df = pd.read_csv(summary_csv_fn)
    except pd.errors.EmptyDataError:
        print(
            f"[skip] results are empty for option = {option}, "
            f"benchmark = {benchmark} (empty {summary_csv_fn})."
        )
        return None

    print(table(summary_df).to_string())

    return summary_df


def merge_summary_dfs(summary_dfs: dict[str, pd.DataFrame | None]) -> pd.DataFrame:
    all_results = []

    for tool_name, summary_df in summary_dfs.items():
        if summary_df is None:
            continue

        summary_df = summary_df.copy()

        for col in ["max_latency", "avg_latency", "avg_ev", "d1"]:
            summary_df[col] = pd.to_numeric(summary_df[col], errors="coerce")

        summary_df_grouped = summary_df.groupby(["formula", "log"])

        for (formula, log), group_df in summary_df_grouped:

            if group_df.empty or group_df["max_latency"].isna().all():
                all_results.append(pd.Series({
                    "tool": tool_name,
                    "formula": formula,
                    "log": log,
                    "a": "t.o.",
                    "real_time": False,
                    "max_latency": "t.o.",
                    "avg_latency": "t.o.",
                    "avg_ev": "t.o.",
                }))
                continue

            avg_s = group_df.mean(numeric_only=True)

            all_results.append(pd.Series({
                "tool": tool_name,
                "formula": formula,
                "log": log,
                "max_latency": avg_s["max_latency"],
                "avg_latency": avg_s["avg_latency"],
                "avg_ev": avg_s["avg_ev"],
            }))

    return pd.DataFrame(all_results)