from subprocess import Popen, PIPE, DEVNULL, STDOUT
from io import StringIO
import os.path

from time import sleep, time
from math import log10

import pandas as pd
import matplotlib.pyplot as plt

from replayer import replay
from generator import random_trace

plt.rcParams["font.family"] = "serif"
plt.rcParams["font.serif"] = "Times New Roman"
plt.rcParams["text.usetex"] = True

OPTION = "WhyMon"
SYNTHETIC = True
SYNTHETIC_N, SYNTHETIC_K = 1000, 10

if OPTION == "Enfpoly":
    COMMAND = '~/Tools/monpoly_dev/monpoly/monpoly -enforce -sig arfelt.sig -formula formulae_enfpoly/{}  -ignore_parse_errors '
elif OPTION == "WhyEnf":
    COMMAND = '../../../../bin/whymon.exe -mode enforce -sig arfelt.sig -formula formulae_whyenf/{} -l'
elif OPTION == "WhyMon":
    COMMAND = '../../../../bin/whymon.exe -mode light -sig arfelt.sig -formula formulae_whymon/{} -l'
  

TEMP = "temp.txt"

PREFIX = "> LATENCY "
SUFFIX = " <"

def summary(df, step, a):
    return {"avg_time": df["out_time"].diff().mean(),
            "max_time": df["out_time"].diff().max()}

def run_whymon(formula, step, a, n, k):
    command = COMMAND.format(formula)
    print(command)
    if SYNTHETIC:
        random_trace(n, k, "synthetic.log")
        log_fn = "synthetic.log"
        max_tp = n - 1
    else:
        log_fn = "special.log"
        max_tp = 4240
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
    if SYNTHETIC:
        real_time = 1000 / a
    else:
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
    if SYNTHETIC:
        ax.set_title(f"“{desc}” policy, acceleration $a$ = {a:.0f}")
    else:
        ax.set_title(f"“{desc}” policy, acceleration $a$ = {a:.0f} (1 second = {a / (24*3600):.0f} days)")
    ax.legend(loc=('upper left'))
    fig.tight_layout()
    fig.savefig(fn, dpi=1000)

if __name__ == '__main__':
    FORMULAE1 = {
        "Consent": "arfelt_4_consent",
        "Sharing": "arfelt_7_erasure_3",
        "Lawfulness": "arfelt_3_lawfulness",
        "Information": "arfelt_5_information",
        "Limitation": "arfelt_2_limitation",
        "Deletion": "arfelt_7_erasure",
    }
    if OPTION == "WhyEnf":
        FORMULAE = FORMULAE1
    elif OPTION == "WhyMon":
        FORMULAE = { k: v for (k, v) in FORMULAE1.items() if k not in ["Limitation"] }
    elif OPTION == "Enfpoly":
        FORMULAE = {
            "Consent": "arfelt_4_consent",
            "Lawfulness": "arfelt_3_lawfulness",
        }
    series = []
    STEP = 100
    if OPTION == "Enfpoly":
        OUT = "out_enfpoly"
    elif OPTION == "WhyEnf":
        OUT = "out_whyenf"
    elif OPTION == "WhyMon" :
        OUT = "out_whymon"
    a = 1e6
    N = 1
    ONLY_GRAPH = False

    if SYNTHETIC:
        summary_fn = f"summary_{SYNTHETIC_N}_{SYNTHETIC_K}.csv"
        graph_fn = f"graph_{SYNTHETIC_N}_{SYNTHETIC_K}.png"
    else:
        summary_fn = "summary.csv"
        graph_fn = "graph.png"

    if not ONLY_GRAPH:
    
        for desc, formula in FORMULAE.items():

            pairs = [(SYNTHETIC_K, n) for n in [100, 400, 1600, 6400, 25600]] + \
                [(k, SYNTHETIC_N) for k in [1, 4, 16, 64, 256]]
    
            for (k, n) in pairs:
                for i in range(N):
                    df = run_whymon(formula + ".mfotl", STEP, a, n, k)
                    if df is None:
                        print('timed out')
                        continue
                    if SYNTHETIC:
                        csv_fn = f"{formula}_{a}_{n}_{k}.csv"
                        png_fn = f"{formula}_{a}_{n}_{k}.png"
                    else:
                        csv_fn = f"{formula}_{a}.csv"
                        png_fn = f"{formula}_{a}.png"
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
                
    for desc in FORMULAE1:
        s_max = summary[(summary["formula"] == desc) & (summary["n"] == SYNTHETIC_N)][["k", "max_time"]].groupby("k").mean()
        s_avg = summary[(summary["formula"] == desc) & (summary["n"] == SYNTHETIC_N)][["k", "avg_time"]].groupby("k").mean()
        ax_k.plot(s_avg.index, s_avg["avg_time"], label=f'“{desc}” ($\mathsf{{avg}}_t$)', linewidth=1.5)

    for desc in FORMULAE1:
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
        
    

