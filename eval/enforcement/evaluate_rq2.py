from subprocess import Popen, PIPE, DEVNULL, STDOUT
from io import StringIO
import os.path

import argparse

from time import sleep, time
from math import log10

import pandas as pd
import matplotlib.pyplot as plt

from replayer import replay
from generator import random_trace

plt.rcParams["font.family"] = "serif"
plt.rcParams["font.serif"]  = "Times New Roman"
plt.rcParams["text.usetex"] = True

### Constants

FORMULAE_ENFPOLY = {
    "Consent":    "consent",
    "Lawfulness": "lawfulness",
}

FORMULAE_WHYENF = {
    "Consent":     "consent",
    "Sharing":     "sharing",
    "Lawfulness":  "lawfulness",
    "Information": "information",
    "Limitation":  "limitation",
    "Deletion":    "deletion",
    "GDPR":        "gdpr",
}

SIG = "examples/arfelt_et_al_2019.sig"
LOG = "examples/arfelt_et_al_2019_repeatable.log"

SUMMARY = "summary.csv"
TABLE   = "table.csv"
GRAPH   = "graph.png"
  
PREFIX  = "> LATENCY "
SUFFIX  = " <"

### End constants

def summary(df, step, a):
    return {"a": a,
            "n_ev": df["n_ev"].sum(),
            "n_tp": df["n_tp"].sum(),
            "cau": df["cau"].sum(),
            "sup": df["sup"].sum(),
            "ins": df["ins"].sum(),
            "avg_ev": df["n_ev"].sum() / (df["time"].max()-df["time"].min()) * 1000,
            "avg_latency": df["latency"].mean(),
            "avg_time": df["out_time"].diff().mean(),
            "max_time": df["out_time"].diff().max(),
            "max_latency": df["latency"].max()}

def table(df):
    series = []
    for formula, formula_df in df.groupby("formula"):
        avg_df = formula_df.groupby(["formula", "a", "d1"]).mean()
        ok_avg_df = avg_df[avg_df["max_latency"] <= avg_df.index.get_level_values("d1")].sort_index()
        best_avg_s = ok_avg_df.iloc[-1]
        series.append(pd.Series({"formula": formula,
                                 "a": ok_avg_df.index.get_level_values("a")[-1],
                                 "avg_latency": best_avg_s["avg_latency"],
                                 "max_latency": best_avg_s["max_latency"],
                                 "avg_time": best_avg_s["avg_time"],
                                 "max_time": best_avg_s["max_time"],
                                 "avg_ev": best_avg_s["avg_ev"]}))
    return pd.DataFrame(series)

def run_whymon(formula, step, a):
    command = COMMAND.format(SIG, formula)
    max_tp = 4240
    df = replay(LOG, max_tp, command, acc=a)
    series = []
    df = df.set_index(["type", "tp"])
    for (t, tp) in df.index:
        if t == 'f':
            try:
                the_f = df.loc[('f', tp)]
                the_r = df.loc[('r', tp)]
            except:
                continue
            series.append({'tp': tp,
                           'n_ev': the_r['n_ev'],
                           'n_tp': the_r['n_tp'],
                           'cau': the_r['cau'],
                           'sup': the_r['sup'],
                           'ins': the_r['ins'],
                           'time': the_f['ts'],
                           'latency': the_r['computer_time'] - the_f['computer_time'],
                           'out_time': the_r['computer_time']})
    return pd.DataFrame(series).sort_values(by="tp")

def plot(desc, step, a, df, fn):
    fig, ax = plt.subplots(1, 1, figsize=(7.5, 2.5))
    real_time = (1000*24*3600) / a
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
    ax.set_title(f"“{desc}” policy, acceleration $a$ = {a:.0f} (1 second = {a / (24*3600):.0f} days)")
    ax.legend(loc=('upper left'))
    fig.tight_layout()
    fig.savefig(fn, dpi=1000)
    plt.close()

if __name__ == '__main__':

    parser = argparse.ArgumentParser()
    parser.add_argument("option", help="Backend to test (Enfpoly, WhyEnf, or WhyMon)")
    parser.add_argument("-e", "--executable-path", help="Path to Enfpoly or WhyMon (for options Enfpoly and WhyMon)")
    parser.add_argument("-g", "--only-graph", action='store_true', help="Only generate the graph (do not run experiments)")
    parser.add_argument("-s", "--smoke-test", action='store_true', help="Only run smoke test (do not run experiments)")
    args = parser.parse_args()

    OPTION = args.option
    EXE = args.executable_path
    ONLY_GRAPH = args.only_graph
    SMOKE_TEST = args.smoke_test

    if OPTION == "Enfpoly":
        COMMAND  = EXE + ' -enforce -sig {} -formula examples/formulae_enfpoly/{} -ignore_parse_errors '
        FORMULAE = FORMULAE_ENFPOLY
        OUT      = "out_enfpoly"
    elif OPTION == "WhyEnf":
        COMMAND  = '../../bin/whyenf.exe -sig {} -formula examples/formulae_whyenf/{}'
        FORMULAE = FORMULAE_WHYENF
        OUT      = "out_whyenf"
    elif OPTION == "WhyMon":
        COMMAND  = EXE + ' -mode light -sig {} -formula examples/formulae_whymon/{}'
        FORMULAE = { k: v for (k, v) in FORMULAE_WHYENF.items() if k not in ["Limitation"] }
        OUT      = "out_whymon" 
    
    series        = []
    STEP          = 100
    if SMOKE_TEST:
        ACCELERATIONS = [5.12e7]
    else:
        ACCELERATIONS = [1e5, 2e5, 4e5, 8e5, 1.6e6, 3.2e6, 6.4e6, 1.28e7, 2.56e7, 5.12e7]
    N             = 10

    print(f"Running evaluation for RQ2-3 on logs from Arfelt et al. (2019), OPTION = {OPTION}, SMOKE_TEST = {SMOKE_TEST}")

    if not ONLY_GRAPH:
    
        for desc, formula in FORMULAE.items():

             for a in ACCELERATIONS:

                for it in range(N):
                    print(f"OPTION = {OPTION}, formula = {desc}, a = {a}, it = {it+1}")
                    df = run_whymon(formula + ".mfotl", STEP, a)
                    csv_fn = f"{formula}_{a}.csv"
                    png_fn = f"{formula}_{a}.png"
                    df.to_csv(os.path.join(OUT, csv_fn), index=False)
                    summ = summary(df, STEP, a)
                    summ["formula"] = desc
                    plot(desc, STEP, a, df, os.path.join(OUT, png_fn))
                    series.append(summ)
                    print(summ)
            
        summary_df = pd.DataFrame(series)
        summary_df.to_csv(os.path.join(OUT, SUMMARY), index=False)

    summary_df = pd.read_csv(os.path.join(OUT, SUMMARY))

    summary_df = summary_df[["formula", "a", "avg_ev", "avg_latency", "max_latency", "avg_time", "max_time"]]
    summary_df["d1"] = (1000*24*3600) / summary_df["a"]

    print(table(summary_df).to_string())

    fig, ax2 = plt.subplots(1, 1, figsize=(7.5, 3))
    ax = ax2.twinx()
    
    d1 = summary_df[["a", "d1"]].groupby("a").mean()
    ax.plot(d1.index, d1["d1"], "k--", label="$1/a$", linewidth=1.5)
            
    for desc in FORMULAE_WHYENF:
        s = summary_df[summary_df["formula"] == desc][["a", "max_latency"]].groupby("a").mean()
        ax.plot(s.index, s["max_latency"], label=f'“{desc}”', linewidth=1.5)

    ae = summary_df[["a", "avg_ev"]].groupby("a").mean()
    ax2.plot(ae.index, ae["avg_ev"], "k:", label="avg. event rate", linewidth=0.5)

    ax2.set_xlabel("acceleration $a$")
    ax.set_ylabel("max latency $\mathsf{max}_{\ell}(a)$ (ms)")
    ax2.set_ylabel("events/s")

    if OPTION == "WhyEnf":
        ax.legend(loc='upper right')
        ax2.legend(loc='upper left')
        
    ax2.set_xscale('log')
    ax.set_yscale('log')     
    ax2.set_yscale('log')
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, GRAPH), dpi=300)

    plt.close()
        
    

