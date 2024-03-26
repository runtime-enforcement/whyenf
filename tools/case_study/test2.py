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

OPTION = "WhyEnf"
SYNTHETIC = False
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

def run_whymon(formula, step, a):
    command = COMMAND.format(formula)
    print(command)
    if SYNTHETIC:
        random_trace(SYNTHETIC_N, SYNTHETIC_K, "synthetic.log")
        log_fn = "synthetic.log"
        max_tp = SYNTHETIC_N - 1
    else:
        log_fn = "special.log"
        max_tp = 4240
    df = replay(log_fn, max_tp, command, acc=a)
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
    #ax.set_ylabel('ms/event')
    ax.set_xlabel("time elapsed (s)")
    #ax.set_ylim([0, 17])
    #ax2 = ax.twinx()
    #ax2.plot(df["time"], df["n_ev"] * 1000 / step, 'b-', label='log(event rate)', linewidth=0.5)
    #ax2.set_ylabel('log(event/s)', color='b')
    #ax2.set_yscale('log')
    #ax.set_yscale('log')
    #ax2.tick_params(axis='y', labelcolor='b')
    if SYNTHETIC:
        ax.set_title(f"“{desc}” policy, acceleration $a$ = {a:.0f}")
    else:
        ax.set_title(f"“{desc}” policy, acceleration $a$ = {a:.0f} (1 second = {a / (24*3600):.0f} days)")
    ax.legend(loc=('upper left'))
    #ax2.legend(loc='upper left', labelcolor='b')
    fig.tight_layout()
    fig.savefig(fn, dpi=1000)

# number of caused and suppressed events


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
    ACCELERATIONS = [1e5, 2e5, 4e5, 8e5, 1.6e6, 3.2e6, 6.4e6, 1.28e7, 2.56e7, 5.12e7]
    N = 1
    ONLY_GRAPH = True

    if SYNTHETIC:
        summary_fn = f"summary_{SYNTHETIC_N}_{SYNTHETIC_K}.csv"
        graph_fn = f"graph_{SYNTHETIC_N}_{SYNTHETIC_K}.png"
    else:
        summary_fn = "summary.csv"
        graph_fn = "graph.png"

    if not ONLY_GRAPH:
    
        for desc, formula in FORMULAE.items():

            for a in ACCELERATIONS:
                for _ in range(N):
                    df = run_whymon(formula + ".mfotl", STEP, a)
                    if SYNTHETIC:
                        csv_fn = f"{formula}_{a}_{SYNTHETIC_N}_{SYNTHETIC_K}.csv"
                        png_fn = f"{formula}_{a}_{SYNTHETIC_N}_{SYNTHETIC_K}.png"
                    else:
                        csv_fn = f"{formula}_{a}.csv"
                        png_fn = f"{formula}_{a}.png"
                    df.to_csv(os.path.join(OUT, csv_fn), index=False)
                    summ = summary(df, STEP, a)
                    summ["formula"] = desc
                    #a = summ["real_time_acc"]
                    plot(desc, STEP, a, df, os.path.join(OUT, png_fn))
                    series.append(summ)
                    print(summ)
            
        summary = pd.DataFrame(series)
        summary.to_csv(os.path.join(OUT, summary_fn), index=None)

    summary = pd.read_csv(os.path.join(OUT, summary_fn))

    summary = summary[["formula", "a", "avg_ev", "avg_latency", "max_latency", "avg_time", "max_time"]]
    if SYNTHETIC:
        summary["d1"] = 1000 / summary["a"]
    else:        
        summary["d1"] = (1000*24*3600) / summary["a"]

    fig, ax2 = plt.subplots(1, 1, figsize=(7.5, 3))
    ax = ax2.twinx()
    
    d1 = summary[["a", "d1"]].groupby("a").mean()
    ax.plot(d1.index, d1["d1"], "k--", label="$1/a$", linewidth=1.5)
            
    for desc in FORMULAE1:
        s = summary[summary["formula"] == desc][["a", "max_latency"]].groupby("a").mean()
        ax.plot(s.index, s["max_latency"], label=f'“{desc}”', linewidth=1.5)


    print(summary)
    
    ae = summary[["a", "avg_ev"]].groupby("a").mean()
    ax2.plot(ae.index, ae["avg_ev"], "k:", label="avg. event rate", linewidth=0.5)

    ax2.set_xlabel("acceleration $a$")
    ax.set_ylabel("max latency $\mathsf{max}_{\ell}(a)$ (ms)")
    ax2.set_ylabel("events/s")

    if OPTION == "WhyEnf":
        ax.legend(bbox_to_anchor=(0, 1.02, 1, 0.2), loc="lower left",
                  mode="expand", borderaxespad=0, ncol=4)
        ax2.legend(loc='upper left')
    ax2.set_xscale('log')
    ax.set_yscale('log')     
    ax2.set_yscale('log')
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, graph_fn), dpi=300)
        
    

