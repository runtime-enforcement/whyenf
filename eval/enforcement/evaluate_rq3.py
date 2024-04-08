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
plt.rcParams["font.serif"] = "Times New Roman"
#plt.rcParams["text.usetex"] = True

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
}

SIG = "examples/arfelt_et_al_2019.sig"
LOG = "examples/arfelt_et_al_2019_repeatable.log"

TEMP = "temp.txt"

PREFIX = "> LATENCY "
SUFFIX = " <"

### End constants

def summary(df, step, a):
    return {"avg_time": df["out_time"].diff().mean(),
            "max_time": df["out_time"].diff().max()}

def run_whymon(formula, step, a, n, k):
    command = COMMAND.format(SIG, formula)
    random_trace(n, k, "synthetic.log")
    log_fn = "synthetic.log"
    max_tp = n - 1
    df = replay(log_fn, max_tp, command, acc=a)
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
    real_time = 1000 / a
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
    ax.set_title(f"“{desc}” policy, acceleration $a$ = {a:.0f}")
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
    if OPTION == "Enfpoly":
        EXE = args.executable_path or '../../../monpoly/monpoly'
    else:
        EXE = args.executable_path or '../../../whymon/bin/whymon.exe'
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
    
    series                   = []
    STEP                     = 100
    a                        = 1e6
    N                        = 1
    SYNTHETIC_N, SYNTHETIC_K = 1000, 10
    summary_fn               = f"summary_{SYNTHETIC_N}_{SYNTHETIC_K}.csv"
    graph_fn                 = f"graph_{SYNTHETIC_N}_{SYNTHETIC_K}.png"

    print(f"Running evaluation for RQ3 on synthetic logs, OPTION = {OPTION}, SMOKE_TEST = {SMOKE_TEST}")

    if not ONLY_GRAPH:
    
        for desc, formula in FORMULAE.items():

            if SMOKE_TEST:
                pairs = [(SYNTHETIC_K, SYNTHETIC_N)]
            else:
                pairs = [(SYNTHETIC_K, n) for n in [100, 400, 1600, 6400, 25600]] + \
                    [(k, SYNTHETIC_N) for k in [1, 4, 16, 64, 256]]
    
            for (k, n) in pairs:
                
                for it in range(N):
                    
                    print(f"OPTION = {OPTION}, formula = {desc}, a = {a}, n = {n}, k = {k}, it = {it+1}")
                    df = run_whymon(formula + ".mfotl", STEP, a, n, k)
                    if df is None:
                        print('timed out')
                        continue
                    csv_fn = f"{formula}_{a}_{n}_{k}.csv"
                    png_fn = f"{formula}_{a}_{n}_{k}.png"
                    df.to_csv(os.path.join(OUT, csv_fn), index=False)
                    summ = summary(df, STEP, a)
                    summ["formula"] = desc
                    summ["k"] = k
                    summ["n"] = n
                    plot(desc, STEP, a, df, os.path.join(OUT, png_fn))
                    series.append(summ)
                    print(summ)
            
        summary = pd.DataFrame(series)

    summary = pd.read_csv(os.path.join(OUT, summary_fn))

    summary = summary[["formula", "k", "n", "avg_time", "max_time"]]

    fig_k, ax_k = plt.subplots(1, 1, figsize=(7.5, 3))
    fig_n, ax_n = plt.subplots(1, 1, figsize=(7.5, 3))
                
    for desc in FORMULAE_WHYENF:
        s_max = summary[(summary["formula"] == desc) & (summary["n"] == SYNTHETIC_N)][["k", "max_time"]].groupby("k").mean()
        s_avg = summary[(summary["formula"] == desc) & (summary["n"] == SYNTHETIC_N)][["k", "avg_time"]].groupby("k").mean()
        ax_k.plot(s_avg.index, s_avg["avg_time"], label=f'“{desc}” ($\mathsf{{avg}}_t$)', linewidth=1.5)

    for desc in FORMULAE_WHYENF:
        s_max = summary[(summary["formula"] == desc) & (summary["k"] == SYNTHETIC_K)][["n", "max_time"]].groupby("n").mean()
        s_avg = summary[(summary["formula"] == desc) & (summary["k"] == SYNTHETIC_K)][["n", "avg_time"]].groupby("n").mean()
        ax_n.plot(s_avg.index, s_avg["avg_time"], label=f'“{desc}” ($\mathsf{{avg}}_t$)', linewidth=1.5)

    ax_k.set_xlabel("$k$")
    ax_n.set_xlabel("$n$")
    ax_k.set_ylabel("Processing time (ms)")
    ax_n.set_ylabel("Processing time (ms)")
    ax_k.set_xscale("log")
    ax_n.set_xscale("log")
    ax_k.set_yscale("log")
    ax_n.set_yscale("log")
    ax_k.legend(loc='upper left')
    ax_n.legend(loc='upper left')

    fig_k.tight_layout()
    fig_n.tight_layout()
    fig_k.savefig(os.path.join(OUT, "k_" + graph_fn), dpi=300)
    fig_n.savefig(os.path.join(OUT, "n_" + graph_fn), dpi=300)
    plt.close()
        
    

