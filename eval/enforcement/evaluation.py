import os.path
from pathlib import Path
from tqdm import tqdm

from typing import Any, Dict, List, Optional

import pandas as pd
import matplotlib.pyplot as plt

from replayer import replay

plt.rcParams["font.family"] = "serif"
plt.rcParams["font.serif"]  = "Times New Roman"
plt.rcParams["text.usetex"] = True

def summary(df: pd.DataFrame, a: float, time_unit: float) -> Dict[str, Any]:
    return {"a"          : a,
            "d1"         : (time_unit * 1000) / a,
            "n_ev"       : df["n_ev"].sum(),
            "n_tp"       : df["n_tp"].sum(),
            "cau"        : df["cau"].sum(),
            "sup"        : df["sup"].sum(),
            "ins"        : df["ins"].sum(),
            "avg_ev"     : df["n_ev"].sum() / (df["time"].max()-df["time"].min()) * 1000,
            "avg_latency": df["latency"].mean(),
            "avg_time"   : df["out_time"].diff().mean(),
            "max_time"   : df["out_time"].diff().max(),
            "max_latency": df["latency"].max()}

def table(df: pd.DataFrame) -> pd.DataFrame:
    series = []
    for (formula, log), formula_log_df in df.groupby(["formula", "log"]):
        avg_df = formula_log_df.groupby(["formula", "log", "a", "d1"]).mean()
        ok_avg_df = avg_df[avg_df["max_latency"] <= avg_df.index.get_level_values("d1")].sort_index()
        if ok_avg_df.shape[0] > 0:
            best_avg_s = ok_avg_df.iloc[-1]
            series.append(pd.Series({"formula"    : formula,
                                    "log"        : log,
                                    "a"          : ok_avg_df.index.get_level_values("a")[-1],
                                    "avg_latency": best_avg_s["avg_latency"],
                                    "max_latency": best_avg_s["max_latency"],
                                    "avg_time"   : best_avg_s["avg_time"],
                                    "max_time"   : best_avg_s["max_time"],
                                    "avg_ev"     : best_avg_s["avg_ev"]}))
    return pd.DataFrame(series)

def run_tool(command: str, log: Path, a: float, desc: str, to: int) -> Optional[pd.DataFrame]:
    print(command)
    max_tp = len(open(log, 'r').readlines()) - 1
    df = replay(log, max_tp, command, desc=desc, acc=a, to=to)
    if df is None:
        return None
    series = []
    df = df.set_index(["type", "tp"])
    for (t, tp) in df.index:
        if t == 'f':
            try:
                the_f = df.loc[('f', tp)]
                the_r = df.loc[('r', tp)]
            except:
                continue
            series.append({'tp'      : tp,
                           'n_ev'    : the_r['n_ev'],
                           'n_tp'    : the_r['n_tp'],
                           'cau'     : the_r['cau'],
                           'sup'     : the_r['sup'],
                           'ins'     : the_r['ins'],
                           'time'    : the_f['ts'],
                           'latency' : the_r['computer_time'] - the_f['computer_time'],
                           'out_time': the_r['computer_time']})
    return pd.DataFrame(series).sort_values(by="tp")

def name_of_time_unit(time_unit: int) -> str:
    if time_unit == 1:
        return "seconds"
    elif time_unit == 60:
        return "minutes"
    elif time_unit == 60*60:
        return "hours"
    elif time_unit == 60*60*24:
        return "days"
    elif time_unit == 60*60*24*365:
        return "years"
    else:
        return ""

def plot(formula: str, log: str, a: float, df: pd.DataFrame, fn: Path, time_unit: int) -> None:
    fig, ax = plt.subplots(1, 1, figsize=(7.5, 2.5))
    real_time = (1000 * time_unit) / a
    df["time"] /= 1000
    ax.plot(df["time"], df["latency"], 'k-', label='latency (ms)', linewidth=0.5)
    ax.plot([min(df["time"]), max(df["time"])], [real_time, real_time], 'k:', label="real-time latency $1/a$ (ms)", linewidth=0.5)
    ax.plot([min(df["time"]), max(df["time"])], [max(df["latency"]), max(df["latency"])], 'k--', label="max latency $\mathsf{max}_{\ell}(a)$ (ms)", linewidth=0.5)
    df_ev = df[df["n_ev"] > 0]
    ax.plot(df_ev["time"], df_ev["n_ev"], 'b|', label='trace events', markersize=2)
    df_cau = df[df["cau"] > 0]
    ax.plot(df_cau["time"], df_cau["cau"], 'go', label='caused events', markersize=2)
    df_sup = df[df["sup"] > 0]
    ax.plot(df_sup["time"], df_sup["sup"], 'r^', label='suppressed events', markersize=2)
    ax.set_xlabel("time elapsed (s)")
    ax.set_title(f"Formula = {formula}, log = {log}, acceleration $a$ = {a:.0f} (1 second = {a / time_unit:.0f} {name_of_time_unit(time_unit)})")
    ax.legend(loc=('upper left'))
    fig.tight_layout()
    fig.savefig(str(fn), dpi=1000)
    plt.close()

def summary_plot(summary_df: pd.DataFrame, formulae: Dict[str, str], logs: Dict[str, str], fn: Path) -> None:
    fig, ax2 = plt.subplots(1, 1, figsize=(7.5, 3))
    ax = ax2.twinx()
    
    d1 = summary_df[["a", "d1"]].groupby("a").mean()
    ax.plot(d1.index, d1["d1"], "k--", label="$1/a$", linewidth=1.5)
            
    for formula_desc in formulae:
        for log_desc in logs:
            s = summary_df[(summary_df["formula"] == formula_desc) & (summary_df["log"] == log_desc)][["a", "max_latency"]].groupby("a").mean()
            ax.plot(s.index, s["max_latency"], label=f'{formula_desc}, {log_desc}', linewidth=1.5)

    ae = summary_df[["a", "avg_ev"]].groupby("a").mean()
    ax2.plot(ae.index, ae["avg_ev"], "k:", label="avg. event rate", linewidth=0.5)

    ax2.set_xlabel("acceleration $a$")
    ax.set_ylabel("max latency $\mathsf{max}_{\ell}(a)$ (ms)")
    ax2.set_ylabel("events/s")
        
    ax2.set_xscale('log')
    ax.set_yscale('log')     
    ax2.set_yscale('log')
    fig.tight_layout()
    fig.savefig(str(fn), dpi=300)
    plt.close()

def run_experiments(
        option        : str, 
        benchmark     : str, 
        exe           : str, 
        accelerations : List[float],
        only_graph    : bool = False, 
        n             : int  = 10,
        time_unit     : int  = 1,
        to            : int  = 600,
        func          : bool = False,
) -> None:
    # Set benchmark path and output folder
    benchmark_path = Path('benchmarks') / benchmark / option
    formulae_path  = benchmark_path / 'formulae'
    logs_path      = benchmark_path / 'logs'
    out_path       = Path('outputs')    / benchmark / option
    if not os.path.exists(out_path):
        os.makedirs(out_path)
    summary_csv_fn = out_path / 'summary.csv'
    summary_png_fn = out_path / 'summary.png'

    # Build command to be called
    command : str = ""
    if   option == "enfpoly":
        command = exe + ' -enforce -sig {} -formula ' + str(formulae_path) + '/{} -ignore_parse_errors'
    elif option == "whyenf":
        command = exe + ' -sig {} -formula ' + str(formulae_path) + '/{}'
    elif option == "lifeboat":
        command = exe + ' -sig {} -formula ' + str(formulae_path) + '/{}'
    else:
        raise ValueError("Invalid option " + option)
    if func:
        command += ' -func ' + str(benchmark_path / 'functions.py')
    
    # Find formulae, logs, signature
    formulae : Dict[str, str] = { fn.split(".")[0]: fn for fn in os.listdir(formulae_path) }
    logs     : Dict[str, str] = { fn.split(".")[0]: fn for fn in os.listdir(logs_path) }
    sig_fn   : Path           = benchmark_path / 'signature.sig'

    # Perform experiments
    series : List[Dict[str, Any]] = []
    total_steps = len(formulae) * len(logs) * len(accelerations) * n
    desc = f"option = {option}, benchmark = {benchmark}, accelerations = {accelerations[0]}-{accelerations[-1]}, n = {n}"
    t = tqdm(total = total_steps, desc = desc)
    if not only_graph:
    
        for formula_desc, formula_fn in formulae.items():
             
            for log_desc, log_fn in logs.items():

                for a in accelerations:

                    for i in range(n):
                        desc = f"formula = {formula_desc}, log = {log_desc}, a = {a}, it = {i+1}"
                        df = run_tool(command.format(sig_fn, formula_fn), logs_path / log_fn, a, desc, to = to)
                        if df is not None:
                            csv_fn = f"{formula_desc}_{log_desc}_{a}.csv"
                            png_fn = f"{formula_desc}_{log_desc}_{a}.png"
                            df.to_csv(out_path / csv_fn, index=False)
                            summ = summary(df, a, time_unit)
                            summ["formula"] = formula_desc
                            summ["log"] = log_desc
                            plot(formula_desc, log_desc, a, df, out_path / png_fn, time_unit)
                            series.append(summ)
                        t.update()
                
        summary_df = pd.DataFrame(series)
        summary_df.to_csv(summary_csv_fn, index=False)

    # Open and print summary
    summary_df = pd.read_csv(summary_csv_fn)
    print(table(summary_df).to_string())

    # Generate summary plot
    summary_plot(summary_df, formulae, logs, summary_png_fn)


